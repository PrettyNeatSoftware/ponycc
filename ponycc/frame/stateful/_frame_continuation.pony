class _FrameContinuation[V: FrameVisitor[V, S], S: Any iso]
    embed indices: Array[USize] = []
    let continue_fn: {(Frame[V, S], Any val)} val
    var value: Any val = None

    new create(fn: {(Frame[V, S], Any val)} val) => continue_fn = fn

    fun ref _push_index(idx: USize) => indices.push(idx)

    fun clone(): _FrameContinuation[V, S] iso ^ =>
        let copy = recover _FrameContinuation[V, S](continue_fn) end
        for i in indices.values() do copy._push_index(i) end
        copy.value = value
        consume copy