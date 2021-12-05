
;struc _bitset? _elems?*, _ghost?*
; .elems? = _elems
; .ghost? = _ghost
;end struc

_bitset? := 0H
namespace _bitset?
  calminstruction _declare? _result?*
    assign      _result.=elems?, _constant?._zero?
    assign      _result.=ghost?, _constant?._zero?
  end calminstruction

  calminstruction _destroy? _result?*
    restore     _result.=elems?, _result.=elems?
  end calminstruction
                         
  calminstruction _remove_unnamed? _result?*
    local       _useless
    evaluate    _useless, _result.=ghost?
    cmp         _useless, _constant?._false?
    jyes        _remove_unnamed_finish
    _call       _destroy, _result
   _remove_unnamed_finish:
  end calminstruction

  calminstruction _duplicate? _result?*, _bitset?*
    movvar      _result.=elems?, _bitset.=elems?
    movvar      _result.=ghost?, _bitset.=ghost?
  end calminstruction

  iterate <_kind?*,_operator_1?*,_operator_2?>, _insert,or,, _delete,and,not
    calminstruction _kind? _result?*, _item?*
      local         _value
      _balance      _item, {}
      jno           _kind#_finish
      varrfsh       _item
      arrange       _value, _result.=elems?
      _operator_1   _value, (_operator_2 (1H shl _item))
      assign        _result.=elems?, _value
     _kind#_finish:
    end calminstruction
  end iterate

  iterate <_kind?*,_call?*>, _inserts,_insert, _deletes,_delete
    calminstruction _kind? _result?*, _items?*&
      local     _item, _list
      _balance  _items, {}
      jno       _kind#_finish
      _iterate  _item, _items
        arrange _list, {_item}
        call    _call, _result, _list
      _end      _iterate
     _kind#_finish:
    end calminstruction
  end iterate

  calminstruction _length? _result?*, _bitset?*
    arrange     _bitset, _bitset.=elems?
    call        _popcnt, _result, _bitset
  end calminstruction

  calminstruction _empty? _result?*, _bitset?*
    arrange     _bitset, _bitset.=elems?
    varrfsh     _bitset
    cmpz        _bitset
    not         _bitset
    jyes        _empty_publish
    setz        _bitset
   _empty_publish:
    publish     _result, _bitset
  end calminstruction

  calminstruction _member? _result?*, _bitset?*, _item?*
    local       _return
    setz        _return
    _balance    _item, {}
    jno         _member_publish
    arrange     _bitset, _bitset.=elems?
    check       (_bitset and (1H shl _item))
    jno         _member_publish
    not         _return
   _member_publish:
    publish     _result, _return
  end calminstruction

  ; XXX USELESS
  calminstruction _singleton? _result?*, _bitset?*
    local       _return
    _init       const __return, _return
    call        _length, __return, _bitset
    cmp         _return, 1H
    jno         _singleton_finish
    arrange     _return, (=bsf _bitset#.=elems?)
    varrfsh     _return
    publish     _result, _return
   _singleton_finish:
  end calminstruction

  calminstruction _anonymous? _result?*, _literal?*&
    _balance    _literal, {}
    jno         _anonymous_finish
    _call       _unique, ~ _result, anonymous
    transform   _result
    _call       _declare, ~ _result
    assign      _result.=ghost?, _constant?._true?
    arrange     _literal, {_literal}
    _call       _inserts, ~ _result, ~ _literal
   _anonymous_finish:
  end calminstruction
 
  calminstruction _blit? _result?*, _bitset?*&
    _call       _anonymous, _bitset, ~ _bitset
    _call       _duplicate, ~ _result, ~ _bitset
    _call       _remove_unnamed, ~ _bitset
  end calminstruction

  iterate <_kind?*,_operator?*>, _union,or, _intersection,and
    calminstruction _kind? _result?*, _bitset?*&
      local     _value
      _call     _anonymous, _bitset, ~ _bitset
      arrange   _value, ((_result.=elems?) =_operator (_bitset.=elems?))
      varrfsh   _value
      assign    _result.=elems?, _value
      _call     _remove_unnamed, ~ _bitset
    end calminstruction
  end iterate

  calminstruction _element? _result?*, _bitset?*, _position?*
    local       _value, _offset, _bitmask, _iterator
    _cstwrp     _bitmask
    _cstwrp     _position
    _asmcmd     =assert (_position >== 0H)
    setz        _offset
    arrange     _value, _bitset.=elems?
    varrfsh     _value
   _element_loop:
    cmpz        _value
    jyes        _element_finish
    add         _offset, (bsf _value)
    compute     _value, (_value shr (bsf _value))
    compute     _bitmask, (_value and 0FFH)    
    ;_asmcmd     =load __bitmask:=byte =from =_btcnt:__bitmask
    loadvar     byte, _bitmask, _btcnt:_bitmask
    check       ((_position - _bitmask) < 0H)
    jno         _element_update
   _element_find:
    cmpz        _position
    jyes        _element_publish
    compute     _value, (_value xor (1H shl (bsf _value)))
    dec         _position
    jump        _element_find
   _element_update:
    sub         _position, _bitmask
    shr         _value, 8H
    add         _offset, 8H
    jump        _element_loop
   _element_publish:
    add         _offset, (bsf _value)
    publish     _result, _offset
   _element_finish:
  end calminstruction

  _generate_foreach bitset, _declare?, _duplicate?, _element?, _insert?, _length?

  calminstruction _difference? _result?*, _bitset?*&
    local           _item, _lookup
    _call           _anonymous, _bitset, ~ _bitset
    _bitset_foreach _bitset, _item
      arrange       _lookup, {_item}
      _call         _delete, ~ _result, ~ _lookup
    _end            _foreach
    _call           _remove_unnamed, ~ _bitset
  end calminstruction

  macro calminstruction?._incsub? _return?*, __return?*, _destination?*, _target?*, _goto?*, _update?*
    call    _bitset?._subset?, __return, _destination, _target
    cmpz    _return
    _goto
    call    _bitset?._union?, _destination, _target
    _update
  end macro

  macro calminstruction?._incmbr? _return?*, __return?*, _destination?*, _item?*, _goto?*, _update?*
    call    _bitset?._member?, __return, _destination, _item
    cmpz    _return
    _goto
    call    _bitset?._insert?, _destination, _item
    _update
  end macro

  calminstruction _subset? _result?*, _bitset_1?*, _bitset_2?*
    local           _temporary, _empty
    _call           _unique, _temporary, subset
    _call           _anonymous, _bitset_1, ~ _bitset_1
    _call           _anonymous, _bitset_2, ~ _bitset_2
    _call           _duplicate, ~ _temporary, ~ _bitset_1
    _call           _difference, ~ _temporary, ~ _bitset_2
    _call           _empty, _empty, ~ _temporary
    publish         _result, _constant?._false?
    cmpz            _empty 
    jyes            _subset_finish
    publish         _result, _constant?._true?
   _subset_finish:
    _call           _remove_unnamed, ~ _bitset_1
    _call           _remove_unnamed, ~ _bitset_2
    _call           _destroy, ~ _temporary
  end calminstruction

  calminstruction _common_element? _result?*, _bitset_1?*, _bitset_2?*
    local       _temporary, _return
    _cstwrp     _temporary
    _cstwrp     _return
    _cstwrp     common
    call        _unique, __temporary, _common
    call        _duplicate, _temporary, _bitset_1
    call        _intersection, _temporary, _bitset_2
    call        _empty, __return, _temporary
    not         _return
    publish     _result, _return
  end calminstruction

  calminstruction _equivalent? _result?*, _bitset_1?*, _bitset_2?*
    local       _value
    _call       _anonymous, _bitset_1, ~ _bitset_1
    _call       _anonymous, _bitset_2, ~ _bitset_2
    arrange     _value, ((_bitset_1.=elems?) - (_bitset_2.=elems?))
    varrfsh     _value
    cmpz        _value
    not         _value
    jyes        _equivalent_publish
    setz        _value
   _equivalent_publish:
    publish     _result, _value
    _call       _remove_unnamed, ~ _bitset_1
    _call       _remove_unnamed, ~ _bitset_2
  end calminstruction

  calminstruction _negate? _result?*, _limit?*
    local       _value
    arrange     _value, _result.=elems?
    varrfsh     _value
    not         _value
    and         _value, ((1H shl _limit) - 1H)
    assign      _result.=elems?, _value
  end calminstruction
 
  iterate <_kind?*,_size?*>, byte,100H, word,10000H
    calminstruction _negate_#_kind? _result?*
      _init       var const _width, _size
      call        _negate, _result, _width
    end calminstruction
  end iterate

  ; XXX USELESS
  calminstruction (_result?) _foreach?: _functor?*, _extras?&
    local       _return, _destination, _predicate, _value, _replace, _element, _first, _last, _vargs
    _init       const __first, _first
    _init       const __last, _last
    _init       const __return, _return
    take        _destination, _result
    take        _predicate, _functor
    take        _vargs, _extras
    push        _value,
    push        _replace,
    push        _first,
    push        _last,
    setz        _replace
    arrange     _value, _destination#.=elems?
    varrfsh     _value
    setz        _first
    setz        _last
    not         _first
   _foreach_loop:
    cmpz        _value
    jyes        _foreach_finish
    compute     _element, _value
    bsf         _element
    cmpz        (_value xor ((1H shl _element)))
    jno         _foreach_continue
    not         _last
   _foreach_continue:
    arrange     _return,
    _asmcmd     __return _predicate {_element}, __first, __last, _vargs
    setz        _first
    xor         _value, (1H shl _element)
    symrfsh     _return
    match       ,_return
    jyes        _foreach_loop
    or          _replace, (1H shl _return)
    jump        _foreach_loop
   _foreach_finish:
    assign      _destination#.=elems?, _replace
    pop         _destination, _predicate, _vargs, _value, _replace, _first, _last
  end calminstruction

  ; XXX USELESS
  calminstruction (_result?) _display_functor? _item?*, _first?*, _last?*, _extras?&
    local       _value
    _balance    _item, {}
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

  calminstruction _display? _result?*
    execute         { display "{" }
    _bitset_foreach _result, _item, _first, _last
      arrange       _value, _item
      stringify     _value
      execute       { display _value }
      varrfsh       _last
      cmpz          _last   
      jyes          _display_separator
      _continue
     _display_separator:
      execute       { display "," }
    _end            _foreach
    execute         { display "}", 00AH }
  end calminstruction
end namespace

