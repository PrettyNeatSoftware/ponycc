
use ".."
use "../../ast"
use "collections"
use "files"

class val ParseProgramFiles is Pass[Sources, Program]
  """
  TODO: Docs for this agreggated pass
  """
  let _resolve_sources: {(String, String): (String, Sources)?} val
  let _load_builtin: Bool val

  fun name(): String => "parse-program-files"

  new val create(resolve_sources': {(String, String): (String, Sources)?} val, load_builtin: Bool = true) =>
    _resolve_sources = resolve_sources'
    _load_builtin = load_builtin

  fun apply(sources: Sources, fn: {(Program, Array[PassError] val)} val) =>
    let engine = _ParseProgramFilesEngine(_resolve_sources, fn)
    if _load_builtin then
      try
        (let builtin_dir, let builtin_sources) = _resolve_sources(".", "builtin")?
        engine.start_builtin(builtin_sources)
      end
    end
    engine.start(sources)

class val AbsPath is (Hashable & Equatable[AbsPath])
  let path: String val
  new val create(str: String) =>
    path = Path.abs(Path.clean(str))
  
  fun eq(that: AbsPath): Bool => path == that.path

  fun hash(): USize => path.hash()

actor _ParseProgramFilesEngine
  let _pending: SetIs[Source]     = _pending.create()
  var _completed: Bool = false
  let _packages: Map[AbsPath, Package] = _packages.create()
  var _errs: Array[PassError] trn = []
  let _complete_fn: {(Program, Array[PassError] val)} val
  let _resolve_sources: {(String, String): (String, Sources)?} val
  var _builtin_use: (UsePackage | None) = None

  new create(
    resolve_sources': {(String, String): (String, Sources)?} val,
    complete_fn': {(Program, Array[PassError] val)} val)
  =>
    (_resolve_sources, _complete_fn) = (resolve_sources', complete_fn')

  be start(sources: Sources, package: Package = Package) =>
    _start(sources, package)
  
  be start_builtin(sources: Sources, package: Package = Package) =>
    _start(sources, package where is_builtin = true)
  
  fun ref _start(sources: Sources, package: Package, is_builtin: Bool = false) =>
    try
      let package_path = AbsPath(Path.dir(sources(0)?.path()))
      if _packages.contains(package_path) then return end

      _packages(package_path) = package

      for source in sources.values() do
        _pending.set(source)
        let this_tag: _ParseProgramFilesEngine = this
        Parse(source, this_tag~after_parse(source, package where is_builtin = is_builtin)) // TODO: fix ponyc to let plain `this` work here
      end
    end

  be after_parse(
    source: Source, package: Package,
    module': Module, errs: Array[PassError] val, is_builtin: Bool = false)
  =>
    var module = consume module'

    // Take note of having finished parsing this source.
    _pending.unset(source)

    // Take note of any errors.
    for err in errs.values() do _errs.push(err) end

    if is_builtin then
      _builtin_use = UsePackage(None, LitString("builtin")).attach_tag[Package](package)
    end

    let use_packages = Array[UsePackage]

    if not is_builtin then
      match _builtin_use | let u: UsePackage => use_packages.push(u) end
    end

    // Call start for the source files of any referenced packages.
    for u' in module.use_decls().values() do
      match u'
      | let u: UseFFIDecl => package.add_ffi_decl(u)
      | let u: UsePackage =>
        try
          (let scheme, let locator) =
            try
              let specifier = u.package().value()
              (let scheme, let locator) = specifier.clone().chop(specifier.find(":")?.usize())
              locator.trim_in_place(1)
              (scheme, locator)
            else ("package", u.package().value())
            end

          match scheme
          | "package" =>
            (let package_path, let sources) =
              _resolve_sources(u.pos().source().path(), u.package().value())?
            

            // TODO: assign same Package to packages with the same absolute path.
            try
              let used_package = _packages(AbsPath(package_path))?
              use_packages.push(u.attach_tag[Package](used_package))
            else
              let new_package = Package
              use_packages.push(u.attach_tag[Package](new_package))
              _start(sources, new_package)
            end
          
          | "lib" => None // used for including libraries
          | "path" => None // setting library search paths
          | "test" => None
          else None // TODO: how do we handle lib schemes?
          end

        else
          _errs.push(PassError(u.package().pos(),
            "Couldn't resolve this package directory."))
        end
      end
    end

    for t in module.type_decls().values() do
      let type_decl = PackageTypeDecl(t)
      for u in use_packages.values() do type_decl.add_use_package(u) end
      package.add_type_decl(type_decl)
    end

    try package.add_doc(module.docs() as LitString) end

    // _packages.push(package)

    _maybe_complete()

  be _maybe_complete() =>
    """
    If there are no more pending sources left, run the completion logic.
    This is in a separate behaviour so that causal message order ensures that
    this happens after any start calls in the same after_parse execution.
    """
    if (_pending.size() == 0) and (not _completed) then _complete() end

  fun ref _complete() =>
    _completed = true
    let program = Program

    // Collect the modules into packages.
    for package in _packages.values() do
      program.add_package(package)
    end

    _complete_fn(program, _errs = [])
