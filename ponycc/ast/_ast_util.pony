
primitive _ASTUtil
  fun parse_lit_integer(pos: SourcePosAny): U128 ? =>
    let str = pos.string().clone() .> replace("_", "")
    str.u128()?
  
  fun parse_lit_float(pos: SourcePosAny): F64 ? =>
    // TODO: fix stdlib String.f64 to error on failure.
    if pos.length() == 0 then error end
    let str = pos.string().clone() .> replace("_", "")
    str.f64()?
  
  fun parse_lit_string(pos: SourcePosAny): String ? =>
    let quotes_length =
      if pos.string().at("\"\"\"")
      then USize(3)
      else USize(1)
      end

    if pos.length() < (2 * quotes_length) then error end

    // TODO: handle escaped characters
    SourcePos(pos.source(), pos.offset() + quotes_length, pos.length() - (2 * quotes_length)).string()

  fun parse_lit_character(pos: SourcePosAny): U8 ? =>
    // TODO: handle escaped characters
    //if pos.length() != 3 then error end
    if pos.length() == 3 then
      return SourcePos(pos.source(), pos.offset() + 1, pos.length() - 2).string()(0)?
    end

    let str = SourcePos(pos.source(), pos.offset() + 1, pos.length() - 2).string()

    if str(0)? != '\\' then error end

    var i: USize = 1

    match str(i)?
    | 'a' => '\a'
    | 'b' => '\b'
    | 'e' => '\e'
    | 'f' => '\f'
    | 'n' => '\n'
    | 'r' => '\r'
    | 't' => '\t'
    | 'v' => '\v'
    | '\\' => '\\'
    | '0' => '\0'
    | '\'' => '\''
    else error // TODO: handle hex escaped \xFF type chars
    end


  
  fun parse_id(pos: SourcePosAny): String ? =>
    if pos.length() == 0 then error end
    pos.string()
