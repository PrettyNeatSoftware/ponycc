use "collections"
use "../../ast"
use "../../pass"
use poly = "../../polyfill"

actor _FrameReactor[V: FrameVisitor[V, S], S: Any iso]
    let _program: Program
    var _state: (S iso | _Placeholder)
    var _complete_fn: _FrameRunnerFn[S]

    let _type_whitelist: (Array[TypeDecl] val | None)
        "If this is set, only visit these types"

    var _expectations: USize = 0
    embed _errs: Array[PassError] = []
    embed _continuations
        : Array[(Program, Package, PackageTypeDecl, _FrameContinuation[V, S] iso)] 
        = []
    embed _ready_to_continue: MapIs[_FrameContinuation[V, S] tag, Any val] = _ready_to_continue.create()

    new create(
        program: Program,
        state: S iso,
        fn: _FrameRunnerFn[S],
        whitelist: (Array[TypeDecl] val | None) = None)
    =>
        (_program, _state, _complete_fn, _type_whitelist) = (program, consume state, fn, whitelist)
        visit_program(program)
    
    be access_state(fn: {(S iso): S iso ^} val) =>
        _state = match _state = _Placeholder
        | let s: S iso => fn(consume s)
        | let p: _Placeholder => consume p
        end
    
    be err(a: AST, s: String) =>
        _errs.push(PassError(a.pos(), s))
    
    be _push_expectation(loc: SourceLoc = __loc) =>
        //@printf[I32]("Push (%s, %u:%u)\n".cstring(), loc.file().cstring(), loc.line(), loc.pos())
        _expectations = _expectations + 1
    be _pop_expectation(loc: SourceLoc = __loc) => 
        //@printf[I32]("Pop (%s, %u:%u)\n".cstring(), loc.file().cstring(), loc.line(), loc.pos())
        _expectations = _expectations - 1
        if _expectations == 0 then _complete(loc) end
    
    be continue_with(c: _FrameContinuation[V, S] tag, value: Any val) =>
        var found = false
        var i: USize = 0 // we dont use index access, but rather remove, so this only keeps track of if we did a full circle, in the case we're searching for something non-existant
        try while i < _continuations.size() do
            i = i + 1
            (let prog, let pkg, let td, let continuation) = _continuations.shift()?
            if continuation is c then
                found = true
                continuation.value = value
                visit_type_decl(prog, pkg, td, consume continuation)
                _pop_expectation()
                break
            else
                _continuations.push((prog, pkg, td, consume continuation))
            end
        end end

        if not found then 
            @printf[I32]("didn't find await continuation\n".cstring())
            _ready_to_continue(c) = value
        end
    
    fun ref _complete(loc: SourceLoc) =>
        if (_continuations.size() > 0) and (_errs.size() == 0) then
            @printf[I32]("Compiler Deadlock\n".cstring())
            _errs.push(PassError(SourcePosNone, "compiler deadlock"))
        end

        poly.Sort[PassError](_errs)
        let copy: Array[PassError] trn = []
        for e in _errs.values() do copy.push(e) end
        match _state = _Placeholder
        | let s: S => (_complete_fn = {(_, _, _) => _})(_program, consume s, consume copy)
        | let p: _Placeholder => consume p ; @printf[I32]("_state == _Placeholder, this shouldn't happen ever!".cstring())
        end
    
    be _track_result(
        program: Program,
        package: Package,
        type_decl: PackageTypeDecl,
        result: (_FrameContinuation[V, S] iso | None) = None)
    =>
        match consume result | let continuation: _FrameContinuation[V, S] iso =>
            if _ready_to_continue.contains(continuation) then
                try
                    (_, let value) = _ready_to_continue.remove(continuation)?
                    continuation.value = value
                    visit_type_decl(program, package, type_decl, consume continuation)
                    _pop_expectation()
                end
            else
                _continuations.push((program, package, type_decl, consume continuation))
            end
        end
    
    fun box should_visit(td: TypeDecl): Bool =>
        match _type_whitelist | let whitelist: Array[TypeDecl] val => whitelist.contains(td)
        else true
        end

    fun tag visit_program(program: Program) =>
        _push_expectation()
        program.access_packages({(packages)(reactor = this) =>
            for package in packages.values() do
                reactor.visit_package(program, package)
            end
            reactor._pop_expectation()
        })
    
    fun tag visit_package(program: Program, package: Package) =>
        _push_expectation()
        package.access_type_decls({(type_decls)(reactor = this) =>
            for type_decl in type_decls.values() do
                reactor.visit_type_decl(program, package, type_decl)
            end
            reactor._pop_expectation()
        })
    
    fun tag visit_type_decl(
        program: Program,
        package: Package,
        type_decl: PackageTypeDecl,
        continue_from: (_FrameContinuation[V, S] val | None) = None)
    =>
        _push_expectation()

        type_decl.access_type_decl({(ast')(reactor: _FrameReactor[V, S] tag = this) =>
            reactor._access_type_decl(program, package, type_decl, continue_from, ast')
            ast'
        })
    
    be _access_type_decl(
        program: Program,
        package: Package,
        type_decl: PackageTypeDecl,
        continue_from: (_FrameContinuation[V, S] val | None),
        ast': TypeDecl)
    =>
        if not should_visit(ast') then
            _pop_expectation()
            return
        end

        let continue_from' = try (continue_from as _FrameContinuation[V, S] val).clone() end
        var ast = ast'

        _track_result(program, package, type_decl,
            recover
                let top = _FrameTop[V, S](this, program, package, type_decl, ast)
                let frame = Frame[V, S]._create_under(top, ast)
                let continuation = frame._visit(consume continue_from')
                ast = top.type_decl()
                match continuation | let c: _FrameContinuation[V, S] =>
                    _push_expectation()
                end
                continuation
            end
        )
        _pop_expectation()
    
