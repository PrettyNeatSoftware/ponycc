
primitive ASTDefs
  fun apply(g: ASTGen) =>
    g.def_actor("_Program")
      .> has_list("packages", "package", "Package")
    
    g.def_actor("Package")
      .> has_list("type_decls", "type_decl", "PackageTypeDecl")
      .> has_list("ffi_decls",  "ffi_decl",  "UseFFIDecl")
      .> has_list("docs",       "doc",       "LitString")
    
    g.def_actor("PackageTypeDecl")
      .> has_list("use_packages", "use_package", "UsePackage")
      .> has_var("type_decl", "TypeDecl")
    
    g.def("Module")
      .> with_scope()
      .> has("use_decls",  "coll.Vec[UseDecl]",  "coll.Vec[UseDecl]")
      .> has("type_decls", "coll.Vec[TypeDecl]", "coll.Vec[TypeDecl]")
      .> has("docs",       "(LitString | None)", "None")
    
    g.def("UsePackage")
      .> in_union("UseDecl")
      .> has("prefix",  "(Id | None)", "None")
      .> has("package", "LitString")
      .> has("guard",       "(Expr | None)", "None")
    
    g.def("UseFFIDecl")
      .> in_union("UseDecl")
      .> has("name",        "(Id | LitString)")
      .> has("return_type", "TypeArgs")
      .> has("params",      "Params")
      .> has("partial",     "(Question | None)")
      .> has("guard",       "(Expr | None)", "None")
    
    for name in [
      "TypeAlias"; "Interface"; "Trait"; "Primitive"; "Struct"; "Class"; "Actor"
    ].values() do
      g.def(name)
        .> in_union("TypeDecl")
        .> has("name",        "Id")
        .> has("cap",         "(Cap | None)",        "None")
        .> has("type_params", "(TypeParams | None)", "None")
        .> has("provides",    "(Type | None)",       "None")
        .> has("members",     "Members",             "Members")
        .> has("at",          "(At | None)",         "None")
        .> has("docs",        "(LitString | None)",  "None")
    end
    
    g.def("Members")
      .> has("fields",  "coll.Vec[Field]",  "coll.Vec[Field]")
      .> has("methods", "coll.Vec[Method]", "coll.Vec[Method]")
    
    for name in ["FieldLet"; "FieldVar"; "FieldEmbed"].values() do
      g.def(name)
        .> in_union("Field")
        .> with_type()
        .> has("name",       "Id")
        .> has("field_type", "Type")
        .> has("default",    "(Expr | None)", "None")
        .> has("docstring",  "(LitString | None)", "None")
    end
    
    for name in ["MethodFun"; "MethodNew"; "MethodBe"].values() do
      g.def(name)
        .> in_union("Method")
        .> with_scope()
        .> has("name",        "Id")
        .> has("cap",         "(Cap | At | None)",   "None")
        .> has("type_params", "(TypeParams | None)", "None")
        .> has("params",      "Params",              "Params")
        .> has("return_type", "(Type | None)",       "None")
        .> has("partial",     "(Question | None)",   "None")
        .> has("guard",       "(Sequence | None)",   "None")
        .> has("body",        "(Sequence | None)",   "None")
        .> has("docs",        "(LitString | None)",  "None")
    end
    
    g.def("TypeParams")
      .> has("list", "coll.Vec[TypeParam]", "coll.Vec[TypeParam]")
    
    g.def("TypeParam")
      .> has("name",       "Id")
      .> has("constraint", "(Type | None)", "None")
      .> has("default",    "(Type | None)", "None")
    
    g.def("TypeArgs")
      .> has("list", "coll.Vec[Type]", "coll.Vec[Type]")
    
    g.def("Params")
      .> has("list",     "coll.Vec[(Param | DontCare)]",   "coll.Vec[(Param | DontCare)]") // TODO: account for case where parser emits ellipsis in multiple argument positions
      .> has("ellipsis", "(Ellipsis | None)", "None")
    
    g.def("Param")
      .> with_type()
      .> has("name",       "Id")
      .> has("param_type", "(Type | None)", "None")
      .> has("default",    "(Expr | None)", "None")
    
    g.def("Sequence")
      .> with_scope() // TODO: doesn't always have a scope...
      .> in_union("Expr")
      .> has("list", "coll.Vec[Expr]", "coll.Vec[Expr]")
    
    for name in [
      "Return"; "Break"; "Continue"; "Error"; "CompileIntrinsic"; "CompileError"
    ].values() do
      g.def(name)
        .> in_union("Jump", "Expr")
        .> has("value", "(Expr | None)", "None")
    end
    
    g.def("IfDefFlag")
      .> in_union("IfDefCond")
      .> has("name", "(Id | LitString)")
    
    g.def("IfDefNot")
      .> in_union("IfDefCond")
      .> has("expr", "IfDefCond")
    
    for name in ["IfDefAnd"; "IfDefOr"].values() do
      g.def(name)
        .> in_union("IfDefBinaryOp", "IfDefCond")
        .> has("left",  "IfDefCond")
        .> has("right", "IfDefCond")
    end
    
    g.def("IfDef")
      .> in_union("Expr")
      .> with_scope()
      .> with_type()
      .> has("condition", "Expr")
      .> has("then_body", "Sequence")
      .> has("else_body", "(Sequence | IfDef | None)", "None")
    
    g.def("IfType")
      .> in_union("Expr")
      .> with_scope()
      .> with_type()
      .> has("sub",       "Type")
      .> has("super",     "Type")
      .> has("then_body", "Sequence")
      .> has("else_body", "(Sequence | IfType | None)", "None")
    
    g.def("If")
      .> in_union("Expr")
      .> with_scope()
      .> with_type()
      .> has("condition", "Sequence")
      .> has("then_body", "Sequence")
      .> has("else_body", "(Sequence | If | None)", "None")
    
    g.def("While")
      .> in_union("Expr")
      .> with_scope()
      .> with_type()
      .> has("condition", "Sequence")
      .> has("loop_body", "Sequence")
      .> has("else_body", "(Sequence | None)", "None")
    
    g.def("Repeat")
      .> in_union("Expr")
      .> with_scope()
      .> with_type()
      .> has("loop_body", "Sequence")
      .> has("condition", "Sequence")
      .> has("else_body", "(Sequence | None)", "None")
    
    g.def("For")
      .> in_union("Expr")
      .> with_scope()
      .> with_type()
      .> has("refs",      "(Id | IdTuple | DontCare)")
      .> has("iterator",  "Sequence")
      .> has("loop_body", "Sequence")
      .> has("else_body", "(Sequence | None)", "None")
    
    g.def("With")
      .> in_union("Expr")
      .> with_scope()
      .> with_type()
      .> has("assigns",   "AssignTuple")
      .> has("body",      "Sequence")
      .> has("else_body", "(Sequence | None)", "None")
    
    g.def("IdTuple") // TODO: implement as Tuple[(Id | IdTuple)]
      .> in_union("Expr") // TODO: remove?
      .> with_type()
      .> has("elements", "coll.Vec[(Id | IdTuple | DontCare)]", "coll.Vec[(Id | IdTuple | DontCare)]")
    
    g.def("AssignTuple") // TODO: implement as Tuple[Assign]
      .> with_type()
      .> has("elements", "coll.Vec[Assign]", "coll.Vec[Assign]")
    
    g.def("Match")
      .> in_union("Expr")
      .> with_scope()
      .> with_type()
      .> has("expr",      "Sequence")
      .> has("cases",     "Cases",             "Cases")
      .> has("else_body", "(Sequence | None)", "None")
    
    g.def("Cases")
      .> with_scope() // to simplify branch consolidation
      .> with_type()
      .> has("list", "coll.Vec[Case]", "coll.Vec[Case]")
    
    g.def("Case")
      .> with_scope()
      .> has("expr",  "(Expr | None)", "None")
      .> has("guard", "(Sequence | None)", "None")
      .> has("body",  "(Sequence | None)", "None")
    
    g.def("Try")
      .> in_union("Expr")
      .> with_type()
      .> has("body",      "Sequence")
      .> has("else_body", "(Sequence | None)", "None")
      .> has("then_body", "(Sequence | None)", "None")
    
    g.def("Consume")
      .> in_union("Expr")
      .> with_type()
      .> has("cap",  "(Cap | None)")
      .> has("expr", "(Reference | This)")
    
    g.def("Recover")
      .> in_union("Expr")
      .> with_type()
      .> has("cap",  "(Cap | None)")
      .> has("expr", "Sequence")
    
    g.def("As")
      .> in_union("Expr")
      .> with_type()
      .> has("expr",    "Expr")
      .> has("as_type", "Type")
    
    for name in [
      "Add"; "AddUnsafe"; "Sub"; "SubUnsafe"
      "Mul"; "MulUnsafe"; "Div"; "DivUnsafe"; "Mod"; "ModUnsafe"
      "LShift"; "LShiftUnsafe"; "RShift"; "RShiftUnsafe"
      "Eq"; "EqUnsafe"; "NE"; "NEUnsafe"
      "LT"; "LTUnsafe"; "LE"; "LEUnsafe"
      "GE"; "GEUnsafe"; "GT"; "GTUnsafe"
      "Is"; "Isnt"; "And"; "Or"; "XOr"
    ].values() do
      g.def(name)
        .> in_union("BinaryOp", "Expr")
        .> with_type()
        .> has("left",    "Expr")
        .> has("right",   "Expr")
        .> has("partial", "(Question | None)", "None")
    end
    
    for name in [
      "Not"; "Neg"; "NegUnsafe"; "AddressOf"; "DigestOf"
    ].values() do
      g.def(name)
        .> in_union("UnaryOp", "Expr")
        .> with_type()
        .> has("expr", "Expr")
    end
    
    for name in ["LocalLet"; "LocalVar"].values() do
      g.def(name)
        .> in_union("Local", "Expr")
        .> with_type()
        .> has("name",       "(Id | DontCare)")
        .> has("local_type", "(Type | None)", "None")
    end
    
    g.def("Assign")
      .> in_union("Expr")
      .> with_type()
      .> has("left",  "Expr")
      .> has("right", "Expr")
    
    g.def("Dot")
      .> in_union("Expr")
      .> with_type()
      .> has("left",  "Expr")
      .> has("right", "Id")
    
    g.def("Chain")
      .> in_union("Expr")
      .> with_type()
      .> has("left",  "Expr")
      .> has("right", "Id")
    
    g.def("Tilde")
      .> in_union("Expr")
      .> with_type()
      .> has("left",  "Expr")
      .> has("right", "Id")
    
    g.def("Qualify")
      .> in_union("Expr")
      .> has("left",  "Expr")
      .> has("right", "TypeArgs")
    
    g.def("Call")
      .> in_union("Expr")
      .> with_type()
      .> has("callable",   "Expr")
      .> has("args",       "Args",              "Args")
      .> has("named_args", "NamedArgs",         "NamedArgs")
      .> has("partial",    "(Question | None)", "None")
    
    g.def("CallFFI")
      .> in_union("Expr")
      .> with_type()
      .> has("name",       "(Id | LitString)")
      .> has("type_args",  "(TypeArgs | None)", "None")
      .> has("args",       "Args",              "Args")
      .> has("named_args", "NamedArgs",         "NamedArgs")
      .> has("partial",    "(Question | None)", "None")
    
    g.def("Args")
      .> has("list", "coll.Vec[Sequence]", "coll.Vec[Sequence]")
    
    g.def("NamedArgs")
      .> has("list", "coll.Vec[NamedArg]", "coll.Vec[NamedArg]")
    
    g.def("NamedArg")
      .> has("name",  "Id")
      .> has("value", "Sequence")
    
    g.def("Lambda")
      .> in_union("Expr")
      .> with_type()
      .> has("method_cap",  "(Cap | None)",            "None")
      .> has("name",        "(Id | None)",             "None")
      .> has("type_params", "(TypeParams | None)",     "None")
      .> has("params",      "Params",                  "Params")
      .> has("captures",    "(LambdaCaptures | None)", "None")
      .> has("return_type", "(Type | None)",           "None")
      .> has("partial",     "(Question | None)",       "None")
      .> has("body",        "Sequence",                "Sequence")
      .> has("object_cap",  "(Cap | None)",            "None")
    
    g.def("BareLambda")
      .> in_union("Expr")
      .> with_type()
      .> has("method_cap",  "(Cap | None)",            "None")
      .> has("name",        "(Id | None)",             "None")
      .> has("type_params", "(TypeParams | None)",     "None")
      .> has("params",      "Params",                  "Params")
      .> has("captures",    "(LambdaCaptures | None)", "None")
      .> has("return_type", "(Type | None)",           "None")
      .> has("partial",     "(Question | None)",       "None")
      .> has("body",        "Sequence",                "Sequence")
      .> has("object_cap",  "(Cap | None)",            "None")
    
    g.def("LambdaCaptures")
      .> has("list", "coll.Vec[LambdaCapture]", "coll.Vec[LambdaCapture]")
    
    g.def("LambdaCapture")
      .> has("name",       "Id")
      .> has("local_type", "(Type | None)", "None")
      .> has("value",      "(Expr | None)", "None")
    
    g.def("Object")
      .> in_union("Expr")
      .> has("cap",      "(Cap | None)",     "None")
      .> has("provides", "(Type | None)",    "None")
      .> has("members",  "(Members | None)", "None")
    
    g.def("LitArray")
      .> in_union("Expr")
      .> has("elem_type", "(Type | None)",   "None")
      .> has("sequence",  "Sequence",        "Sequence")
    
    g.def("Tuple")
      .> in_union("Expr")
      .> with_type()
      .> has("elements", "coll.Vec[Sequence]", "coll.Vec[Sequence]")
    
    g.def("This")
      .> in_union("Expr")
    
    for name in ["LitTrue"; "LitFalse"].values() do
      g.def(name)
        .> in_union("LitBool", "Expr")
    end
    
    g.def_wrap("LitInteger", "U128", "_ASTUtil.parse_lit_integer")
      .> in_union("Expr")
    
    g.def_wrap("LitFloat", "F64", "_ASTUtil.parse_lit_float")
      .> in_union("Expr")
    
    // TODO: Distinguish between LitString and LitStringTriple
    g.def_wrap("LitString", "String", "_ASTUtil.parse_lit_string")
      .> in_union("Expr")
    
    g.def_wrap("LitCharacter", "U8", "_ASTUtil.parse_lit_character")
      .> in_union("Expr")
    
    g.def("LitLocation")
      .> in_union("Expr")
      .> with_type()
    
    g.def("Reference")
      .> with_type()
      .> has("name", "Id")
      .> in_union("Expr")
    
    g.def("DontCare")
      .> with_type()
      .> in_union("Expr")
    
    g.def("PackageRef")
      .> has("name", "Id")
      .> in_union("Expr")
    
    for name in ["MethodFunRef"; "MethodNewRef"; "MethodBeRef"].values() do
      g.def(name)
        .> in_union("MethodRef", "Expr")
        .> with_scope()
        .> has("receiver", "Expr")
        .> has("name",     "(Id | TypeArgs)") // TODO: don't use this weird scheme
    end
    
    g.def("TypeRef")
      .> in_union("Expr")
      .> with_type()
      .> has("package", "Expr")
      .> has("name",    "(Id | TypeArgs)") // TODO: don't use this weird scheme
    
    for name in ["FieldLetRef"; "FieldVarRef"; "FieldEmbedRef"].values() do
      g.def(name)
        .> in_union("FieldRef", "Expr")
        .> with_type()
        .> has("receiver", "Expr")
        .> has("name",     "Id")
    end
    
    g.def("TupleElementRef")
      .> in_union("Expr")
      .> with_type()
      .> has("receiver", "Expr")
      .> has("name",     "LitInteger")
    
    for name in ["LocalLetRef"; "LocalVarRef"; "ParamRef"].values() do
      g.def(name)
        .> in_union("LocalRef", "Expr")
        .> with_type()
        .> has("name", "Id")
    end
    
    g.def("ViewpointType")
      .> in_union("Type")
      .> has("left",  "Type")
      .> has("right", "Type")
    
    g.def("UnionType")
      .> in_union("Type")
      .> has("list", "coll.Vec[Type]", "coll.Vec[Type]") // TODO: try to fix the parser compat with this, using seq() instead of _BuildInfix, or at least flattening in the parser first (maybe _BuildInfixFlat?)
    
    g.def("IsectType")
      .> in_union("Type")
      .> has("list", "coll.Vec[Type]", "coll.Vec[Type]") // TODO: try to fix the parser compat with this, using seq() instead of _BuildInfix, or at least flattening in the parser first (maybe _BuildInfixFlat?)
    
    g.def("TupleType")
      .> in_union("Type")
      .> has("list", "coll.Vec[(Type | DontCare)]", "coll.Vec[(Type | DontCare)]") // TODO: confirm parser compat with this
    
    g.def("NominalType")
      .> in_union("Type")
      .> has("name",      "Id")
      .> has("package",   "(Id | None)",           "None")
      .> has("type_args", "(TypeArgs | None)",     "None")
      .> has("cap",       "(Cap | GenCap | None)", "None")
      .> has("cap_mod",   "(CapMod | None)",       "None")
    
    g.def("FunType")
      .> in_union("Type")
      .> has("cap",         "Cap")
      .> has("type_params", "(TypeParams | None)", "None")
      .> has("params",      "Params",              "Params")
      .> has("return_type", "(Type | None)",       "None")
    
    g.def("LambdaType")
      .> in_union("Type")
      .> has("method_cap",  "(Cap | None)",          "None")
      .> has("name",        "(Id | None)",           "None")
      .> has("type_params", "(TypeParams | None)",   "None")
      .> has("param_types", "TupleType",             "TupleType")
      .> has("return_type", "(Type | None)",         "None")
      .> has("partial",     "(Question | None)",     "None")
      .> has("object_cap",  "(Cap | GenCap | None)", "None")
      .> has("cap_mod",     "(CapMod | None)",       "None")
    
    g.def("BareLambdaType")
      .> in_union("Type")
      .> has("method_cap",  "(Cap | None)",          "None")
      .> has("name",        "(Id | None)",           "None")
      .> has("type_params", "(TypeParams | None)",   "None")
      .> has("param_types", "TupleType",             "TupleType")
      .> has("return_type", "(Type | None)",         "None")
      .> has("partial",     "(Question | None)",     "None")
      .> has("object_cap",  "(Cap | GenCap | None)", "None")
      .> has("cap_mod",     "(CapMod | None)",       "None")
    
    g.def("TypeParamRef")
      .> in_union("Type")
      .> has("name",    "Id")
      .> has("cap",     "(Cap | GenCap | None)", "None")
      .> has("cap_mod", "(CapMod | None)",       "None")
    
    g.def("ThisType")
      .> in_union("Type")
    
    g.def("DontCareType")
      .> in_union("Type")
    
    g.def("ErrorType")
      .> in_union("Type")
    
    g.def("LiteralType")
      .> in_union("Type")
    
    g.def("LiteralTypeBranch")
      .> in_union("Type")
    
    g.def("OpLiteralType")
      .> in_union("Type")
    
    for name in ["Iso"; "Trn"; "Ref"; "Val"; "Box"; "Tag"].values() do
      g.def(name)
        .> in_union("Cap", "Type")
    end
    
    for name in [
      "CapRead"; "CapSend"; "CapShare"; "CapAlias"; "CapAny"
    ].values() do
      g.def(name)
        .> in_union("GenCap", "Type")
    end
    
    for name in ["Aliased"; "Ephemeral"].values() do
      g.def(name)
        .> in_union("CapMod")
    end
    
    g.def("At")
    
    g.def("Question")
    
    g.def("Ellipsis")
    
    g.def("Annotation")
    
    g.def("Semicolon")
      .> in_union("Expr") // only so we can nicely error for semicolon at EOL.
      .> has("list", "coll.Vec[Expr]")
    
    g.def_wrap("Id", "String", "_ASTUtil.parse_id")
      .> in_union("Expr") // TODO: remove?
    
    for name in [
      "EOF"
      "NewLine"
      "Use"
      "Colon"
      "Comma"
      "Constant"
      "Pipe"
      "Ampersand"
      "SubType"
      "Arrow"
      "DoubleArrow"
      "AtLBrace"
      "LBrace"
      "RBrace"
      "LParen"
      "RParen"
      "LSquare"
      "RSquare"
      "LParenNew"
      "LBraceNew"
      "LSquareNew"
      "SubNew"
      "SubUnsafeNew"
      "In"
      "Until"
      "Do"
      "Else"
      "ElseIf"
      "Then"
      "End"
      "Var"
      "Let"
      "Embed"
      "Where"
    ].values() do
      g.def_lexeme(name)
        .> in_union("Lexeme")
    end
