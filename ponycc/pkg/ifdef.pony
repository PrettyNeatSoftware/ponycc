use "../ast"
use "../unreachable"

primitive IfdefCondNormalise
	fun apply(cond': AST): IfDefCond ? =>
		match cond'
		| let c: And =>
			match c.partial() | let _: Question => error end
			IfDefAnd(IfdefCondNormalise(c.left())?, IfdefCondNormalise(c.right())?)
		| let c: Or =>
			match c.partial() | let _: Question => error end
			IfDefOr(IfdefCondNormalise(c.left())?, IfdefCondNormalise(c.right())?)
		| let c: Not =>
			IfDefNot(IfdefCondNormalise(c.expr())?)
		| let c: LitString =>
			IfDefFlag(c)
		| let c: Reference =>
			let name = c.name()
			if name.value() == "posix" then
				IfDefOr(
					IfDefOr(
						IfDefFlag(Id("linux")),
						IfDefFlag(Id("osx"))
					),
					IfDefFlag(Id("bsd"))
				)
			else
				IfDefFlag(c.name())
			end
		| let c: Sequence => IfdefCondNormalise(c(0)? as AST)?
		// TODO seq
		| let c: IfDefCond => c // already normalized
		else Unreachable(cond'.string()) ; error
		end