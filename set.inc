
; XXX remove and take bitset? instead

;struc _set? _elems?*, _count?*
;   define .elems? _elems
;   .count? = _count
;end struc

_set? := 0H
namespace _set?
  calminstruction (_result?) _declare?
    local       _target, _value
    arrange     _target, _result#.=elems?
    arrange     _value,
    publish     _target, _value
    setz        _value
    arrange     _target, _result#.=count?
    publish     _target, _value
  end calminstruction

  calminstruction (_result?) _duplicate? _set?*
    local       _destination, _target
    arrange     _target, _set#.=elems?
    transform   _target
    arrange     _destination, _result#.=elems?
    publish     _destination, _target
    arrange     _target, _set#.=count?
    varrfsh     _target
    arrange     _destination, _result#.=count?
    publish     _destination, _target
  end calminstruction

  calminstruction (_result?) _insert? _item?*
    local       _return, __member, _value, _return
    _initsym    __return, _return
    _initsym    __member, _member
    match       {_item}, _item
    jno         _insert_finish
    varrfsh     _item
    _asmcmd     __return __member _result, {_item}
    cmpz        _return
    jno         _insert_finish
    arrange     _return, _result#.=count?
    compute     _value, (_return + 1H)
    publish     _return, _value
    arrange     _return, _result#.=elems?
    check       (_value = 1H)
    arrange     _value, _item
    jyes        _insert_publish
    arrange     _value, _return
    transform   _value
    arrange     _value, _value=,_item
   _insert_publish:
    publish     _return, _value
   _insert_finish:
  end calminstruction

  calminstruction (_result?) _inserts? _items?*&
    local       __insert, _front, _remain
    _initsym    __insert, _insert
    match       {_items}, _items
    jno         _inserts_finish
    arrange     _remain, _items,
   _inserts_loop:
    match       _front=,_remain?, _remain
    jno         _inserts_finish
    _asmcmd     _result __insert {_front}
    jump        _inserts_loop
   _inserts_finish:
  end calminstruction

  calminstruction (_result?) _delete? _item?*
    local       __member, __return, _return, _value, _front, _remain, _list
    _initsym    __member, _member
    _initsym    __return, _return
    match       {_item}, _item
    jno         _delete_finish
    _asmcmd     __return __member _result, {_item}
    cmpz        _return
    jyes        _delete_finish
    arrange     _return, _result#.=count?
    compute     _value, (_return - 1H)
    publish     _return, _value
    arrange     _return, _result#.=elems?
    arrange     _remain, _return,
    transform   _remain
    arrange     _list,
    cmpz        _value
    jyes        _delete_publish
   _delete_loop:
    match       _front=,_remain?, _remain
    jno         _delete_publish
    check       (_front = _item)
    jyes        _delete_loop
    append      _list, _front
    jump        _delete_loop
   _delete_publish:
    publish     _return, _list
   _delete_finish:
  end calminstruction

  calminstruction (_result?) _singleton? _set?*
    local       _value
    arrange     _value, _set#.=count?
    varrfsh     _value
    check       (_value = 1H)
    jno         _singleton_element_finish
    arrange     _value, _set#.=elems
    varrfsh     _value
    publish     _result, _value
   _singleton_element_finish:
  end calminstruction

  calminstruction (_result?) _deletes? _items?*&
    local       __delete, _front, _remain
    _initsym    __delete, _delete
    match       {_items}, _items
    jno         _deletes_finish
    arrange     _remain, _items,
   _deletes_loop:
    match       _front=,_remain?, _remain
    jno         _deletes_finish
    _asmcmd     _result __delete {_front}
    jump        _deletes_loop  
   _deletes_finish:
  end calminstruction

  calminstruction (_result?) _length? _set?*
    arrange     _set, _set#.=count?
    varrfsh     _set
    publish     _result, _set
  end calminstruction

  calminstruction (_result?) _empty? _set?*
    arrange     _set, _set#.=count?
    varrfsh     _set
    cmpz        _set
    jyes        _empty_publish
    setz        _set
    not         _set
   _empty_publish:
    publish     _result, _set
  end calminstruction

  calminstruction (_result?) _member? _set?*, _item?*
    local       _return, _front, _remain
    _initsym    const __return, _return
    _initsym    const __empty, _empty
    match       {_item}, _item
    jno         _member_finish
    _asmcmd     __return __empty _set
    cmpz        _return
    jyes        _member_publish
    setz        _return
    varrfsh     _item
    arrange     _remain, _set#.=elems?
    transform   _remain
   _member_loop:
    match       ,_remain
    jyes        _member_publish
    match       _front=,_remain, _remain
    jyes        _member_compare
    arrange     _front, _remain
    arrange     _remain,
   _member_compare:
    check       (_front = _item)
    jno         _member_loop
    not         _return
   _member_publish:
    publish     _result, _return
   _member_finish:
  end calminstruction

  calminstruction (_result?) _union? _set?*&
    local       __inserts
    _initsym    __inserts, _inserts
    match       {_set}, _set
    jyes        _union_merge
    arrange     _set, _set#.=elems?
    transform   _set
   _union_merge:
    _asmcmd     _result __inserts {_set}
  end calminstruction

  calminstruction (_result?) _intersection? _set?*&
    local       __member, __return, _return, _list, _front, _remain, _newcnt
    _initsym    __member, _member
    _initsym    __return, _return
    match       {_set}, _set
    jyes        _intersection_filter
    arrange     _set, _set#.=elems?
    transform   _set
   _intersection_filter:
    arrange     _remain, _set,
    arrange     _list,
    setz        _newcnt
   _intersection_loop:
    match       _front=,_remain?, _remain
    jno         _intersection_publish
    _asmcmd     __return __member _result, {_front} 
    cmpz        _return
    jyes        _intersection_loop
    inc         _newcnt
    varrfsh     _front
    append      _list, _front
    jump        _intersection_loop
   _intersection_publish:
    arrange     _return, _result#.=count?
    publish     _return, _newcnt
    arrange     _return, _result#.=elems?
    publish     _return, _list
  end calminstruction

  calminstruction (_result?) _equivalent? _set_1?*, _set_2?*
    local       __member, __return, _length_1, _length_2, _return, _remain, _front
    _initsym    __member, _member
    _initsym    __return, _return
    setz        _return
    arrange     _length_1, _set_1#.=count?
    varrfsh     _length_1
    arrange     _length_2, _set_2#.=count?
    varrfsh     _length_2
    check       (_length_1 = _length_2)
    jno         _equivalent_publish
    not         _return
    cmpz        _length_1
    jyes        _equivalent_publish
    arrange     _remain, _set_2#.=elems?,
    transform   _remain
   _equivalent_loop:
    match       _front=,_remain?, _remain
    jno         _equivalent_publish
    _asmcmd     __return __member _set_1, {_front}
    cmpz        _return
    jno         _equivalent_loop
   _equivalent_publish:
    publish     _result, _return
  end calminstruction

  calminstruction (_result?) _foreach?: _functor?*, _extras?&
    local       _return, _destination, _predicate, _vargs, _list, _remain, _front, _first, _last, _counter
    _initsym    const __return, _return
    _initsym    const __first, _first
    _initsym    const __last, _last
    take        _destination, _result
    take        _predicate, _functor
    take        _vargs, _extras
    push        _remain, _destination#.=elems?,
    transform   _remain
    push        _list,
    push        _counter, 0H
    setz        _first
    not         _first
   _foreach_loop:
    match       _front=,_remain?, _remain
    jno         _foreach_finish
    setz        _last
    match       ,_remain
    jno         _foreach_invoke
    not         _last
   _foreach_invoke:
    arrange     _return,
    _asmcmd     __return _predicate {_front}, __first, __last, _vargs
    setz        _first
    symrfsh     _return
    match       ,_return
    jyes        _foreach_loop
    varrfsh     _return
    append      _list, _return
    inc         _counter
    jump        _foreach_loop
   _foreach_finish:
    assign      _destination#.=count?, _counter
    assign      _destination#.=elems?, _list
    pop         _destination, _predicate, _vargs, _remain, _list, _counter
  end calminstruction

  calminstruction (_result?) _negate? _limit?*
    local       _return, _index, _list, _counter
    _initsym    const __return, _return
    _initsym    const __member, _member
    arrange     _list,
    setz        _index
    setz        _counter
   _negate_loop:
    check       (_index < _limit)
    jno         _negate_publish
    _asmcmd     __return __member _result, {_index}
    cmpz        _return
    jno         _negate_update
    append      _list, _index
    inc         _counter
   _negate_update:
    inc         _index
    jump        _negate_loop
   _negate_publish:
    assign      _result#.=count?, _counter
    assign      _result#.=elems?, _list
  end calminstruction

  calminstruction (_result?) _display_functor? _item?*, _first?*, _last?*, _extras?&
    local       _value
    match       {_item}, _item 
    jno         _display_functor_finish
    varrfsh     _item
    varrfsh     _first
    cmpz        _first
    jyes        _display_functor_print
    execute     { display "{" }
   _display_functor_print:
    arrange     _value, _item
    stringify   _value
    execute     { display _value }
    varrfsh     _last
    cmpz        _last   
    jyes        _display_functor_separator
    execute     { display "}", 00AH }
    jump        _display_functor_publish
   _display_functor_separator:
    execute     { display "," }
   _display_functor_publish:
    publish     _result, _item
   _display_functor_finish:
  end calminstruction
 
  macro _display? _target?*
    _target _set?._foreach? _set?._display_functor?
  end macro
end namespace

