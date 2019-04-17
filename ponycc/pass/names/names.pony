
use ".."
use "../../ast"
use "../../frame/stateful"

primitive Names is (Pass[Program, Program] & FrameVisitor[Names, NoState])
  """
  The purpose of the Names pass is...

  This pass only adds attachments to the AST, and is idempotent.
  """
  fun name(): String => "names"

  fun apply(ast: Program, fn: {(Program, Array[PassError] val)} val) =>
    FrameRunner[Names, NoState](ast, NoState, {(p, s, e) => fn(p, e)})
    None

  fun visit[A: AST val](frame: Frame[Names, NoState], ast: A) =>
		match ast | let ast': (LocalLet | LocalVar | FieldLet | FieldVar | FieldEmbed | Param | TypeParam | MethodFun | MethodNew | MethodBe) =>
      try
        let name' = (ast'.name() as Id).value()
        frame.parent()._1.with_scope({(s: Scope) => s.set(name', ast)})
      end
		end
