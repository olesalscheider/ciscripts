#!/usr/bin/env ruby
# vim: set sw=4 sts=4 et tw=80 :

# Copyright 2014 Alex Elsayed <eternaleye@gmail.com>
# Distributed under the terms of the GNU General Public License v2

# This is a script to, given a list of one or more installed
# packages, determine what their actual dependencies are via
# inspection of the DT_NEEDED entries of their installed ELF
# files.

# It requires dev-ruby/ruby-elf::philantrop in order to parse
# said files

require 'Paludis'
require 'getoptlong'
require 'pathname'
require 'weakref'

# dev-ruby/ruby-elf::philantrop
require 'elf'

OPEN_FILES_SOFT_LIMIT = Process.getrlimit(Process::RLIMIT_NOFILE)[0]

# Files reverse lookup table that scans whole system if none of pre-scanned
# packages already provides requested one. This speedups negative result for
# detecting undeclared dependencies.
class FilesRevLookupTable
    def initialize( environment, root )
        @environment = environment
        @root = root
        @lookup = Hash.new { |h,k| h[k] = [] }
        @packages = Hash.new {}
    end

    def scan_package( pkgid )
        return if @packages == :all or @packages.has_key?( pkgid )
        pkgid.contents and pkgid.contents.each do |file|
            if file.instance_of?( Paludis::ContentsFileEntry )
                file.each_metadata do |meta|
                    if meta.instance_of?( Paludis::MetadataFSPathKey )
                        @lookup[meta.parse_value] << pkgid
                    end
                end
            end
        end
        @packages[pkgid] = nil # mark as already processed
    end

    def scan_all
        return if @packages == :all
        packages = @environment[
            Paludis::Selection::AllVersionsUnsorted.new(
                Paludis::FilteredGenerator.new(
                    Paludis::Generator::All.new(),
                    Paludis::Filter::InstalledAtRoot.new( @root )
                )
            )
        ]
        packages.each { |pkgid| scan_package( pkgid ) }
    end

    def scan_deps( deps, pkgid = nil, processed = {} )
        # some code borrowed from ruby/uxample_dep_tree
        deps.each do |dep|
            case dep
            when Paludis::PackageDepSpec
                pkgids = @environment[
                        Paludis::Selection::AllVersionsGroupedBySlot.new(
                            Paludis::FilteredGenerator.new(
                                Paludis::Generator::Matches.new( dep, pkgid, [] ),
                                Paludis::Filter::InstalledAtRoot.new( @root )
                            )
                        )
                    ]
                pkgids.each { |pkgid| scan_package( pkgid ) }
            when Paludis::ConditionalDepSpec
                scan_deps( dep, pkgid, processed )
            when Paludis::NamedSetDepSpec
                set = @environment.set( dep.name )
                if ! set
                    puts "Can't resolve set #{dep.name}"
                elsif processed.has_key?( dep.name )
                    # puts "Recursion at #{dep.name}"
                else
                    processed[dep.name] = nil
                    scan_deps( set, pkgid, processed )
                end
            when Paludis::DependenciesLabelsDepSpec
                scan_deps( dep.labels, pkgid, processed )
            when Paludis::AllDepSpec, Paludis::AnyDepSpec
                scan_deps( dep, pkgid, processed )
            when Paludis::DependenciesLabel, Paludis::BlockDepSpec
                # skip labels and blockers
            else
                raise TypeError, "Got dep of unexpected type #{dep.inspect}"
            end
        end
    end

    def []( filename )
        pkgid = @lookup.fetch( filename, nil )
        if pkgid == nil and @packages != :all
            # puts "Can't find #{filename} (fall-back to global scan)"
            scan_all
            return self[ filename ]
        else
            return pkgid
        end
    end
end

# Take a list of dep spec strings, parse them, look up
# the matching package IDs, and flatten the result into
# a one-level list
def expand_user_targets( environment, root, targets )
    targets.map { |target_str|
        environment[
            # Use ...GroupedBySlot so the output is in the most
            # useful ordering in the case of wildcards and such
            Paludis::Selection::AllVersionsGroupedBySlot.new(
                Paludis::FilteredGenerator.new(
                    Paludis::Generator::Matches.new(
                       Paludis.parse_user_package_dep_spec(
                           target_str,
                           environment,
                           [ :allow_wildcards, :no_disambiguation ]
                       ),
                       nil,
                       []
                    ),
                    Paludis::Filter::InstalledAtRoot.new( root )
                )
            )
        ]
    }.flatten()
end

# Round up all the elves that are in a PackageID,
def enum_elf_contents( pkgid )
    Enumerator.new do |enum|
        pkgid.contents.grep( Paludis::ContentsFileEntry ).each do |file|
            file.each_metadata do |meta|
                next unless meta.instance_of?( Paludis::MetadataFSPathKey )
                begin
                    elf = Elf::File.open( meta.parse_value )

                    # Filter out split debug files
                    next if elf.path.end_with?( '.debug' )

                    begin
                        enum.yield elf
                    ensure
                        elf.close
                    end
                rescue Errno::ENOENT
                    next
                rescue Elf::File::NotAnELF
                    next
                end
            end
        end
    end
end

# Round up all the elves that are in a PackageID,
# grouped by their ELF class
def get_elf_contents( pkgid )
    elves = Hash.new {|h,k| h[k]=Hash.new}

    enum_elf_contents( pkgid ).each do |elf|
        elves[elf.elf_class][elf.path] = elf.clone
    end

    return elves
end

# Apply https://github.com/Flameeyes/ruby-elf/pull/2
class Elf::OsAbi
    # introduce new method based on code in binutils for Linux
    def linux_compatible?;
        [Elf::OsAbi::SysV, Elf::OsAbi::Linux].include?(self)
    end
end

class Elf::File
    # override original method with almost the same content, but with a more
    # correct ABI check
    def is_compatible(other)
        raise TypeError.new("wrong argument type #{other.class} (expected Elf::File)") unless
        other.is_a? Elf::File

        compatible_abi = (@abi.linux_compatible? && other.abi.linux_compatible?) \
            || ([@abi, @abi_version] == [other.abi, other.abi_version])

        @elf_class == other.elf_class and
            @data_encoding == other.data_encoding and
            @version == other.version and
            @machine == other.machine and
            compatible_abi
    end
end

# Apply https://github.com/Flameeyes/ruby-elf/pull/3 (WeakRefs)
class Elf::Utilities::FilePool
    @pool = Hash.new

    # override original to use WeakRef instead of strong one
    def self.[](file)
        realfile = Pathname.new(file).realpath

        cached = @pool[realfile].__getobj__ rescue nil
        if cached.nil? || cached.closed?
            cached = Elf::File.new(realfile)
            @pool[realfile] = WeakRef.new(cached)
        end

        cached
    end

    # add method to clear pool if threshold reached
    # by default threshold is 0 (clear always)
    def self.clear(threshold = 0)
        return if @pool.size < threshold

        # ensure all files closed
        @pool.each_value do |cached_weak|
            cached = cached_weak.__getobj__ rescue nil
            next if cached.nil? || cached.closed?
            cached.close
        end

        @pool.clear
    end
end

# Apply https://github.com/Flameeyes/ruby-elf/pull/7 (bugfix for RPATH)
class Elf::Dynamic
    # Fix typo in original method
    def complete_library_path
      if @complete_library_path.nil?
        @complete_library_path = Array.new

        # If there is no DT_RUNPATH. RPATH wins over the LD_LIBRARY_PATH
        @complete_library_path.concat rpath if runpath.empty?

        @complete_library_path.concat Elf::Utilities.environment_library_path

        # If there is a DT_RUNPATH it wins over the system library path
        @complete_library_path.concat runpath

        @complete_library_path.concat Elf::Utilities.system_library_path

        @complete_library_path.uniq!
      end

      return @complete_library_path
    end
end

# Get the unique NEEDED libs of a list of ELF files
def get_all_linked_files( elves, hidden_types )
    linked = Hash.new {|h,k| h[k]=Hash.new{|h,k| h[k]=Hash.new}}

    elves.each do |elf|
        elf_class = elf.elf_class
        next unless elf.has_section?( '.dynamic' )

        # Note that pkg-config and libtool sometimes forces linker
        # to add extra -l<lib> flags that isn't used directly. Thus we
        # check that needed lib actually resolves some symbols.

        # Build up lookup table for undefined symbols
        unresolved = elf['.dynsym'].reject {|symbol|
            symbol.name().empty? or symbol.defined? # reject undefined and weird symbols
        }.collect {|symbol| [symbol.name(), true]}.to_h

        # XXX: All libs by some reason have empty symbol (filtered out),
        #      maybe issue in ruby-elf
        elf['.dynamic'].needed_libraries.each_pair do |soname, lib|
            unless lib
                # puts "No files found for #{soname} library needed by #{elf.inspect}"
                next
            end
            # Ensure that we have at least one symbol resolved with this
            # lib.
            needed = lib['.dynsym'].any? {|symbol|
                symbol.defined? and unresolved.has_key?(symbol.name())
            }

            # If we don't care about needed libs, skip
            next if hidden_types.has_key?( :used ) and needed

            # If we don't care about overlinked libs, skip unnecessary
            next if hidden_types.has_key?( :unused ) and not needed

            # Unused libs marked with false
            linked[lib.elf_class][lib.path][elf.path] = needed
            # XXX: False positives possible since we have no info about
            #      how libs were pulled into NEEDED section
        end
    end

    return linked
end

def get_owners_by_elfclass( environment, contents_lookup, ignored, target, linked )
    owners = Hash.new {|h,k| h[k]=Hash.new{|h,k| h[k]=Hash.new{|h,k| h[k]=Hash.new}}}

    linked.each_pair do |elf_class, matching_files|
        matching_files.keys.sort.each do |file|
            contents_lookup[file].each do |owner|
                next if owner == target
                next unless ignored.select { |set|
                    Paludis.match_package_in_set( environment, set, owner, [] )
                }.empty?
                matching_files[file].each do |user, value|
                    owners[elf_class][owner][file][user] = value
                end
            end
        end
    end

    return owners
end

def colorprint( color, text )
    case color
    when :Blue
        puts "\e[34;01m#{text}\e[00;00m"
    when :Orange
        puts "\e[33;02m#{text}\e[00;00m"
    when :Green
        puts "\e[32m#{text}\e[00m"
    end
end

def format_status( status )
    case status
    when :enabled
        "declared, enabled"
    when :disabled
        "declared, supposedly disabled"
    when :undeclared
        "undeclared"
    end
end

def format_unused( used, text )
    if used
        text
    else
        "#{text} (unused)"
    end
end

def format_category( status, categorized, detailed )
    colorprint :Green, "        Dependencies (#{format_status(status)}):"

    categorized[status].sort.each do |package, libs|
        next if libs.values.all? { |x| x.empty? }
        colorprint :Blue, format_unused(
            libs.values.any? { |x| x.values.any? },
            "            #{package}"
        )
        libs.sort.each do |reason, users|
            next if users.empty?
            puts format_unused(
                users.values.any?,
                "                #{reason}"
            )
            if detailed
                users.sort.each do |usedby, needed|
                    colorprint :Orange, format_unused(
                        needed,
                        "                    #{usedby}"
                    )
                end
            end
        end
    end
end

# TODO: Maybe also a --root parameter at some point?
opts = GetoptLong.new(
    [ '--help', '-h', GetoptLong::NO_ARGUMENT ],
    [ '--detailed-linkage', '-d', GetoptLong::NO_ARGUMENT ],
    [ '--hide-deps', '-x', GetoptLong::REQUIRED_ARGUMENT ],
    [ '--hide-libs', '-l', GetoptLong::REQUIRED_ARGUMENT ],
    [ '--ignore-set', '-i', GetoptLong::REQUIRED_ARGUMENT ]
)

Paludis::Log.instance.log_level = Paludis::LogLevel::Warning
Paludis::Log.instance.program_name = $0

env = Paludis::PaludisEnvironment.new

ignored_sets = []
hidden_deps = {}
hidden_libs = {}
detailed_linkage = false

opts.each do |opt, arg|
    case opt
    when '--help'
        puts "Usage: #{$0} [ options ] target [ target... ]"
        puts "Options:"
        puts "    --detailed-linkage, -d   Show what files linked to each library"
        puts "    --hide-deps, -x          Hide dependencies that meet some criteria (may be specified multiple times)"
        puts "        enabled                Declared and enabled"
        puts "        disabled               Declared but disabled"
        puts "        declared               Declared, regardless of enablement"
        puts "        undeclared             Undeclared"
        puts "    --hide-libs, -l          Hide libraries whose linkage meets some criteria"
        puts "        used                   Symbols are used"
        puts "        unused                 Symbols are not used (dependency is due to overlinking)"
        puts "    --ignore-set, -i         Don't list packages matching this set as dependencies"
        exit 0
    when '--detailed-linkage'
        detailed_linkage = true
    when '--hide-deps'
        case arg
        when 'enabled'
            hidden_deps[:enabled] = true
        when 'disabled'
            hidden_deps[:disabled] = true
        when 'declared'
            hidden_deps[:enabled] = true
            hidden_deps[:disabled] = true
        when 'undeclared'
            hidden_deps[:undeclared] = true
        end
    when '--hide-libs'
        case arg
        when 'used'
            hidden_libs[:used] = true
        when 'unused'
            hidden_libs[:unused] = true
        end
    when '--ignore-set'
        ignored_sets << env.set( arg )
    end
end

if ARGV.length < 1
    puts "#{$0} requires at least one target. See #{$0} --help for usage information."
    exit 1
end

user_targets = expand_user_targets( env, '/', ARGV )

contentsmap = FilesRevLookupTable.new( env, '/' )

def pkgid_in_deps( environment, target, pkg, enabled_only = true, deps = (target.dependencies_key.parse_value rescue []) )
    deps.each do |dep|
        case dep
        when Paludis::PackageDepSpec
            if Paludis.match_package( environment, dep, pkg, target, [] )
                return true
            end
        when Paludis::ConditionalDepSpec
            if enabled_only
                if dep.condition_met?( environment, target )
                    if pkgid_in_deps( environment, target, pkg, enabled_only, dep )
                        return true
                    end
                else
                    next
                end
            elsif pkgid_in_deps( environment, target, pkg, enabled_only, dep )
                return true
            end
        when Paludis::DependenciesLabelsDepSpec
            if pkgid_in_deps( environment, target, pkg, enabled_only, dep.labels )
                return true
            end
        when Paludis::DependenciesLabel
            next
        when Paludis::BlockDepSpec
            next
        else
            if pkgid_in_deps( environment, target, pkg, enabled_only, dep )
                return true
            end
        end
    end
    return false
end

# In case if any dep will lead to files that belongs to packages in ignored sets
# we should be ready. Scanning some set (like "system") should be faster than
# scanning all installed packages.
ignored_sets.each { |set| contentsmap.scan_deps( set ) }

user_targets.each do |target|
    if not target.contents or target.contents.grep( Paludis::ContentsFileEntry ).empty?
        puts "#{target} has no contents of type file"
        next
    end

    colorprint :Blue, target

    # Ensure that we have at list 2/3 of file descripts until we reach soft
    # limit. And still try to re-use cached elves.
    Elf::Utilities::FilePool.clear(OPEN_FILES_SOFT_LIMIT/3)

    # We expect lookup for files that belongs to some packages in our
    # dependencies.
    deps = target.dependencies_key
    contentsmap.scan_deps( deps.parse_value, target ) unless deps.nil?

    packages = get_owners_by_elfclass(
        env,
        contentsmap,
        ignored_sets,
        target,
        get_all_linked_files(
            enum_elf_contents( target ),
            hidden_libs
        )
    )

    Elf::Class.each do |elf_class|
        if packages[elf_class].empty?
            # Nothing to see here; move along
            next
        end
        colorprint :Green, "    #{elf_class}:"

        unless packages[elf_class].empty?
            categorized = {
                :enabled => {},
                :disabled => {},
                :undeclared => {}
            }

            packages[elf_class].each_pair do |package, value|
                if pkgid_in_deps( env, target, package )
                    categorized[:enabled][package.to_s] = value
                elsif pkgid_in_deps( env, target, package, false )
                    categorized[:disabled][package.to_s] = value
                else
                    categorized[:undeclared][package.to_s] = value
                end
            end

            [:enabled, :disabled, :undeclared].each do |status|
                next if hidden_deps.has_key?(status)
                unless categorized[status].empty?
                    format_category( status, categorized, detailed_linkage )
                    puts
                end
            end
        end
    end
end

exit( 0 )

