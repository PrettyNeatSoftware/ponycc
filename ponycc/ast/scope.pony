use "collections/persistent"

class val Scope
    let scope: Map[String, AST] val

    new val create(map: Map[String, AST] val = Map[String, AST]) =>
        scope = map
    
    fun apply(k: String): AST ? => scope(k)?

    fun set(k: String, v: AST): Scope => Scope(scope(k) = v)

    fun concat(other: Scope): Scope =>
        Scope(scope.concat(other.scope.pairs()))