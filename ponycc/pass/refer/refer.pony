use "promises"
use "debug"

use ".."
use "../../ast"
use "../../frame/stateful"
use "../../unreachable"

primitive Refer is (Pass[Program, Program] & FrameVisitor[Refer, NoState])
  """
  The purpose of the Refer pass is...

  This pass only adds attachments to the AST, and is idempotent.
  """
  fun name(): String => "refer"

  fun apply(ast: Program, fn: {(Program, Array[PassError] val)} val) =>
    FrameRunner[Refer, NoState](ast, NoState, {(p, s, e) => fn(p, e)})
    None
	
	fun _refer_reference(frame: Frame[Refer, NoState], ast: Reference) =>
		let scope = frame.combined_scopes()
		try
			match scope(ast.name().value())?
			| let def: LocalLet   => frame.replace(LocalLetRef(ast.name()).attach_val[LocalLet](def))
			| let def: LocalVar   => frame.replace(LocalVarRef(ast.name()).attach_val[LocalVar](def))
			| let def: Param 			=> frame.replace(ParamRef(ast.name()).attach_val[Param](def))
			| let def: TypeParam  => frame.replace(TypeParamRef(ast.name()).attach_val[TypeParam](def))
			| let def: Field      => frame.replace(Dot(This, ast.name()).attach_val[Field](def))
			| let def: Method     => frame.replace(Dot(This, ast.name()).attach_val[Method](def))
			else Unreachable
			end
		else
			let p = Promise[(TypeRef | PackageRef)]
			let joiner =
				object tag
					var _expect: USize = 2
					var _complete: Bool = false
					let _p: Promise[(TypeRef | PackageRef)] = p

					be apply(decl: (TypeRef | PackageRef)) =>
						_p(decl)

					be reject() =>
						_expect = _expect - 1
						if _expect == 0 then _p.reject() end
				end
			
			frame.find_type_decl(None, ast.name()).next[None](
				{(decl) => joiner(TypeRef(None, ast.name()).attach_val[TypeDecl](decl))},
				{() => joiner.reject()}
			)

			frame.find_use(ast.name()).next[None](
				{(pkg) => joiner(PackageRef(ast.name()).attach_tag[Package](pkg))},
				{() => joiner.reject()}
			)

			frame.await[(TypeRef | PackageRef)](p, {(frame, decl) =>
				match decl
				| None =>
					let trace = ast.pos().source().path() + ":" + ast.pos().cursor()._1.string()
					Debug("Didn't find reference to " + ast.string() + " " + trace)
				| let ast': (TypeRef | PackageRef) => frame.replace(ast')
				end
			})

		end

  fun visit[A: AST val](frame: Frame[Refer, NoState], ast': A) =>
		match ast'
		| let ast: Reference => _refer_reference(frame, ast)
		end
