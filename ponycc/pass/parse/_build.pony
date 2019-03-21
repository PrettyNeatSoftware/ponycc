
interface val _Build
  new val create()
  fun apply(state: _RuleState, tree: TkTree)

primitive _BuildDefault
  fun apply(state: _RuleState, tree: TkTree) =>
    try (state.tree as TkTree).children.push(tree) end

primitive _BuildInfix
  fun apply(state: _RuleState, tree: TkTree) =>
    try tree.children.unshift(state.tree as TkTree) end
    state.tree = tree

primitive _BuildCustomNominalType
  fun apply(state: _RuleState, tree: TkTree) =>
    var i: USize = 0
    try
      // if we have a package id, it needs to come after the id
      if tree.children.size() == 4 then
        // swap 0 and 1 (package and id)
        _BuildDefault(state, tree.children(0)?)
        _BuildDefault(state, TkTree((tree.tk, tree.pos)))
          i = 1
      else
        _BuildDefault(state, TkTree((tree.tk, tree.pos)))
        _BuildDefault(state, TkTree((Tk[None], tree.children(0)?.pos)))
      end

      while i < tree.children.size() do
        let child = tree.children(i)?
        _BuildDefault(state, child)
        i = i + 1
      end
    end
