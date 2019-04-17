"""
This module is an adaptation of `ponycc/frame`
It extends Frames with 
"""
use "promises"
use "../../ast"
use "../../pass"
use "../../unreachable"

interface val FrameVisitor[V: FrameVisitor[V, S], S: Any iso]
	new val create()
	fun visit[A: AST val](frame: Frame[V, S], ast: A)

primitive FrameVisitorNone[S: Any iso] is FrameVisitor[FrameVisitorNone[S], S]
	fun visit[A: AST val](frame: Frame[FrameVisitorNone[S], S], ast: A) => None

type _FrameRunnerFn[S: Any iso] is {(Program, S iso, Array[PassError] val)} val

class FrameRunner[V: FrameVisitor[V, S], S: Any iso]
	let _reactor: _FrameReactor[V, S]

	new create(
		program: Program,
		initial_state: S iso,
		fn: _FrameRunnerFn[S],
		whitelist: (Array[TypeDecl] val | None) = None)
	=>
		_reactor = _FrameReactor[V, S](program, consume initial_state, fn, whitelist)

class iso NoState
// iso placeholder to use access pattern with iso variable without known constructor
// TODO: maybe just force default constructor in an interface for S?
class iso _Placeholder
	new iso create() => None

actor _Seeker[A: Any #share]
	var _open: USize = 0
	var _found: Bool = false
	let _promise: Promise[A]
	new create(p: Promise[A]) => _promise = p
	be apply(a: A) => if not (_found = true) then _promise(a) end
	be open() => _open = _open + 1
	be close() => _open = _open - 1
		if (not _found) and (_open == 0) then _promise.reject() end


interface IsFrame[V: FrameVisitor[V, S], S: Any iso]
	fun box isolated(): IsFrame[V, S] iso ^
	fun box make_child_val(ast': AST): IsFrame[V, S] val =>
		let upper: IsFrame[V, S] iso = isolated()
		recover Frame[V, S].create_under(consume upper, ast') end

	fun _r(): _FrameReactor[V, S]
	fun err(ast': AST val, msg: String val): None
	fun access_state(fn: {(S iso): S iso ^} val)

	fun ast(): AST
	fun ref replace(ast': AST): None

	fun parent(n: USize = 1): (this->IsFrame[V,S], AST)
	//fun parent_frame(n: USize = 1): this->IsFrame[V, S]

	fun program(): (this->IsFrame[V,S], Program)
	fun package(): (this->IsFrame[V,S], Package)
	fun type_decl(): (this->IsFrame[V,S], TypeDecl)
	fun method(): ((this->IsFrame[V,S], Method) | None)
	fun method_body(): ((this->IsFrame[V,S], Sequence) | None)
	fun constraint(): ((this->IsFrame[V,S], Type) | None)
	fun iftype_constraint(): ((this->IsFrame[V,S], Type) | None)

	fun scope(): (Scope | None)
	fun combined_scopes(): Scope
	fun ref with_scope(fn: {(Scope): Scope} val)

	fun find_type_decl(package_id': (Id | None), id: Id): Promise[TypeDecl]
		fun find_use(package_id': Id): Promise[Package]


class _FrameTop[V: FrameVisitor[V, S], S: Any iso] is IsFrame[V, S]
	let _reactor: _FrameReactor[V, S]
	let _program: Program
	let _package: Package
	let _type_decl: PackageTypeDecl
	var _ast: TypeDecl

	new create(
		reactor': _FrameReactor[V, S],
		program': Program,
		package': Package,
		type_decl': PackageTypeDecl,
		ast': TypeDecl
	) =>
		(_reactor, _program, _package, _type_decl, _ast) = (reactor', program', package', type_decl', ast')
	
	fun box isolated(): IsFrame[V, S] iso ^ =>
		recover _FrameTop[V, S](_r(), _program, _package, _type_decl, _ast) end
	
	fun _r(): _FrameReactor[V, S] => _reactor

	fun err(a: AST, s: String) => _reactor.err(a, s)

	fun access_state(fn: {(S iso): S iso ^} val) =>
			_r().access_state(fn)

	fun ast(): AST => _ast
	fun ref replace(a: AST) => try _ast = a as TypeDecl end

	fun parent(n: USize): (this->IsFrame[V, S], AST) => (this, _ast)

	fun program(): (this->IsFrame[V, S], Program) => (this, _program)
	fun package(): (this->IsFrame[V, S], Package) => (this, _package)
	fun type_decl(): (this->IsFrame[V, S], TypeDecl) => (this, _ast)
	fun method(): ((this->IsFrame[V, S], Method) | None) => None
	fun method_body(): ((this->IsFrame[V, S], Sequence) | None) => None
	fun constraint(): ((this->IsFrame[V, S], Type) | None) => None
	fun iftype_constraint(): ((this->IsFrame[V, S], Type) | None) => None

	fun scope(): (Scope | None) =>
		try _ast.find_attached_val[Scope]()?
		else Unreachable ; Scope
		end
	
	fun combined_scopes(): Scope =>
		try scope() as Scope else Unreachable ; Scope end
	
	fun ref with_scope(fn: {(Scope): Scope} val) =>
		replace(try _ast.attach_val[Scope](fn(scope() as Scope)) as TypeDecl else Unreachable ; Id("") end)

		fun find_use(package_id': Id): Promise[Package] =>
			_reactor._push_expectation()
			let promise = Promise[Package].>next[None](
				{(_) => _reactor._pop_expectation()},
				{() => _reactor._pop_expectation()})
			
			let seeker = _Seeker[Package](promise)
			
			seeker.open()
			_type_decl.access_use_packages({(use_packages)(seeker) =>
				for use_package in use_packages.values() do
					try
						if (use_package.prefix() as Id).value() == package_id'.value() then
							seeker(use_package.find_attached_tag[Package]()?)
						end
					end
				end
				seeker.close()
			})

			promise

	fun find_type_decl(package_id': (Id | None), id: Id): Promise[TypeDecl] =>
		_reactor._push_expectation()
		let promise = Promise[TypeDecl].>next[None](
				{(_) => _reactor._pop_expectation()},
				{() => _reactor._pop_expectation()})
		
		let seeker = _Seeker[TypeDecl](promise)
		match package_id'
		| let package_id: Id =>
			seeker.open()
			_type_decl.access_use_packages({(use_packages)(id, seeker) =>
				for use_package in use_packages.values() do
					if try (use_package.prefix() as Id).value() == package_id.value() else false end then
						try
							let package' = use_package.find_attached_tag[Package]()?
							seeker.open()
							package'.access_type_decls({(type_decls)(id, seeker) =>
								for type_decl in type_decls.values() do
									seeker.open()
									type_decl.access_type_decl({(type_decl)(id, seeker) =>
										if id.value() == type_decl.name().value() then
											seeker(type_decl)
										end
										seeker.close()
										type_decl
									})
								end
								seeker.close()
							})
						end
					end
				end
				seeker.close()
			})
		else // TODO: also access all used packages without an id assignment
			seeker.open()
			_type_decl.access_use_packages({(use_packages)(id, seeker) =>
				for use_package in use_packages.values() do
					match use_package.prefix() | let _: Id => continue end
					try
						let package' = use_package.find_attached_tag[Package]()?
						seeker.open()
						package'.access_type_decls({(type_decls)(id, seeker) =>
							for type_decl in type_decls.values() do
								seeker.open()
								type_decl.access_type_decl({(type_decl)(id, seeker) =>
									if id.value() == type_decl.name().value() then
										seeker(type_decl)
									end
									seeker.close()
									type_decl
								})
							end
							seeker.close()
						})
					end
				end
				seeker.close()
			})

			seeker.open()
			_package.access_type_decls({(type_decls)(id, seeker) =>
				for type_decl in type_decls.values() do
					seeker.open()
					type_decl.access_type_decl({(type_decl)(id, seeker) =>
						if id.value() == type_decl.name().value() then
							seeker(type_decl)
						end
						seeker.close()
						type_decl
					})
				end
				seeker.close()
			})
		end
		promise

class Frame[V: FrameVisitor[V, S], S: Any iso] is IsFrame[V, S]
	let _upper: IsFrame[V, S]
	var _ast: AST
	var _maybe_continuation: (_FrameContinuation[V, S] | None) = None

	new create_under(upper': IsFrame[V, S], ast': AST) =>
		_upper = upper'
		_ast = ast'
	
	fun box isolated(): IsFrame[V, S] iso ^ =>
		let upper = _upper.isolated()
		recover Frame[V, S].create_under(consume upper, _ast) end
	
	fun _r(): _FrameReactor[V, S] => _upper._r()

	fun err(a: AST, msg: String) => _r().err(a, msg)

	fun access_state(fn: {(S iso): S iso ^} val) =>
			_r().access_state(fn)
	
	fun parent(n: USize = 1): (this->IsFrame[V, S], AST) =>
		if n == 0 then (this, _ast) else _upper.parent(n - 1) end
	
	fun ast(): AST => _ast
	
	fun ref replace(replace': AST) =>
		if _ast isnt replace' then
			if parent()._2 is _ast then // TODO: less hacky dealing wiht FrameTop.
				_upper.replace(replace')
			else
				_upper.replace(parent()._2.with_replaced_child(_ast, replace'))
			end
			_ast = replace'
		end
	
	fun program(): (this->IsFrame[V, S], Program) => _upper.program()

	fun package(): (this->IsFrame[V, S], Package) => _upper.package()

	fun type_decl(): (this->IsFrame[V, S], TypeDecl) => _upper.type_decl()

	fun method(): ((this->IsFrame[V, S], Method) | None) =>
		try (this, _ast as Method) else _upper.method() end
	
	fun method_body(): ((this->IsFrame[V, S], Sequence) | None) =>
		match parent()._2 | let m: Method =>
			if _ast is m.body() then
				match m.body() | let b: Sequence => (this, b)
				else None
				end
			else None
			end
		else _upper.method_body()
		end
	
	fun constraint(): ((this->IsFrame[V, S], Type) | None) =>
		match parent()._2
		| let _: TypeArgs => None
		| let t: TypeParam =>
			if _ast is t.constraint() then
				match t.constraint() | let c: Type => (this, c)
				else None
				end
			else None end
		else _upper.constraint()
		end
	
	fun iftype_constraint(): ((this->IsFrame[V, S], Type) | None) =>
		match parent()._2
		| let _: TypeArgs => None
		| let i: IfType =>
			if _ast is i.super() then (this, i.super()) else None end
		else _upper.iftype_constraint()
		end

	fun scope(): (Scope | None) =>
		try _ast.find_attached_val[Scope]()?
		else _upper.scope()
		end
	
	fun combined_scopes(): Scope =>
		var scope' = Scope
		var current: IsFrame[V, S] box = this
		while true do
			match current.scope()
			| let s: Scope => scope' = s.concat(scope')
			else break
			end
			let next = current.parent()._1
			if next is current then break end
			current = next
		end
		scope'
	
	fun ref with_scope(fn: {(Scope): Scope} val) =>
		try
			let old_scope = _ast.find_attached_val[Scope]()?
			let new_scope = fn(old_scope)
			let new_ast = _ast.attach_val[Scope](new_scope)
			replace(new_ast)
		else _upper.with_scope(fn)
		end
	
	fun ref await[A: Any val](
		promise: Promise[A],
		fn: {(Frame[V, S], (A | None))} val)
	=>
		"""
		Cause AST traversal to pause when the curren visit function is done with
		the current Frame, and set it up so that when the given promise is fulfilled
		the given fn will be called with the result (or None if rejected), alongside
		a new mutable Frame that is ready to continue traversing the AST.
		"""
		let continuation = _FrameContinuation[V, S]({(frame, value) =>
			try fn(frame, value as (A | None)) else Unreachable end
		})

		continuation.indices.push(-1)
		_maybe_continuation = continuation

		let c: _FrameContinuation[V, S] tag = continuation

		promise.next[None](
			{(value)(r = _r()) => r.continue_with(c, value)},
			{()(r = _r()) => r.continue_with(c, None)}
		)
	
	fun find_type_decl(package_id': (Id | None), id: Id): Promise[TypeDecl] =>
		_upper.find_type_decl(package_id', id)

	fun find_use(package_id': Id): Promise[Package] =>
		_upper.find_use(package_id')
	
	fun ref _visit(continue_from: (_FrameContinuation[V, S] | None) = None)
		: (_FrameContinuation[V, S] | None)
	=>
		let continue_from_idx =
			match continue_from
			| None => 0
			| let c: _FrameContinuation[V, S] =>
				try
					let idx = c.indices.pop()?
					if idx == -1 then
						c.continue_fn(this, c.value)
						return _maybe_continuation
					end
					idx
				else 0
				end
			end

		for (idx, child) in _ast.pairs() do
			if idx >= continue_from_idx then
				match child | let child_ast: AST =>
					match Frame[V, S].create_under(this, child_ast)._visit(continue_from)
					| let continuation: _FrameContinuation[V, S] =>
						continuation.indices.push(idx)
						return continuation
					end
				end
			end
		end

		_ast.apply_specialised[Frame[V, S]](this,
			{[A: AST val](frame, a: A) => V.visit[A](frame, a)})

		_maybe_continuation