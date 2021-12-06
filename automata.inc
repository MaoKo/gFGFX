
;struc _transition_meta? _trcnt?*, _epsilon_elems?*
;   .trcnt? = _trcnt
;   lookup .charset? indexed by (integer < .trcnt?) return _bitset?
;   lookup .destination? indexed by (integer < .trcnt?) return integer
;   .epsilon? _bitset? _epsilon_elems
;end struc

;struc _automata? _start?*, _stcnt?*, _states_elems?*, _accept_elems?*, _transition_elems?*
;   .start? = _start
;   .stcnt? = _stcnt
;   .states? _bitset? _states_elems
;   .accept? _bitset? _accept_elems
;   .transition? _bitset? _transition_elems
;   lookup .table? indexed by (_bitset?.elems? belong to .transition?) return _transition_meta? struc
;end struc

_automata? := 0H
namespace _automata?
  macro calminstruction?._transition_meta_table? _result?*
    assign    _result.=destination?, _constant?._zero?
    assign    _result.=metachar?, _constant?._zero?
  end macro

  calminstruction _transition_meta? _result?*, _trcnt?*
    local                   _holder
    assign                  _result.=trcnt?, _trcnt
    _transition_meta_table  _result
    arrange                 _holder, _result.=epsilon?
    _call                   _bitset?._declare?, ~ _holder
  end calminstruction

  calminstruction _transition_meta_duplicate? _result?*, _meta?*
    local                   _holder_1, _holder_2, _count, _index
    _transition_meta_table  _result
    movvar                  _result.=trcnt?, _meta.=trcnt?
    evaluate                _count, _meta.=trcnt?
    _repeat                 _count, _index:0H
      movvar                _result.=destination?._index?, _meta.=destination?._index?
      arrange               _holder_1, _result.=charset?._index?
      arrange               _holder_2, _meta.=charset?._index?
      _call                 _bitset?._duplicate?, ~ _holder_1, ~ _holder_2
    _end                    _repeat
    arrange                 _holder_1, _result.=epsilon?
    arrange                 _holder_2, _meta.=epsilon?
    _call                   _bitset?._duplicate?, ~ _holder_1, ~ _holder_2
  end calminstruction

  calminstruction _transition_meta_destroy? _result?*
    local     _count, _index, _holder
    arrange   _count, _result.=trcnt?
    varrfsh   _count
    _repeat   _count, _index:0H
      restore   _result.=destination?._index?
      restore   _result.=charset?._index?
    _end      _repeat
    restore   _result.=trcnt?, _result.=destination?, _result.=charset?
    arrange   _holder, _result.=epsilon?
    _call     _bitset?._destroy?, ~ _holder
  end calminstruction

  macro calminstruction?._table? _result?*
    assign      _result.=table?, _constant?._zero?
  end macro

  calminstruction _declare? _result?*
    local       _holder
    _init       var const _default, _constant?._zero?
    assign      _result.=start?, _default
    assign      _result.=stcnt?, _constant?._zero?
    arrange     _holder, _result.=states?
    _call       _bitset?._declare?, ~ _holder
    arrange     _holder, _result.=accept?
    _call       _bitset?._declare?, ~ _holder
    arrange     _holder, _result.=transition?
    _call       _bitset?._declare?, ~ _holder
    _table      _result
  end calminstruction 

  calminstruction _duplicate? _result?*, _machine?*
    local           _holder_1, _holder_2, _transition, _item
    movvar          _result.=start?, _machine.=start?
    movvar          _result.=stcnt?, _machine.=stcnt?
    arrange         _holder_1, _result.=states?
    arrange         _holder_2, _machine.=states?
    _call           _bitset?._duplicate?, ~ _holder_1, ~ _holder_2
    arrange         _holder_1, _result.=accept?
    arrange         _holder_2, _machine.=accept?
    _call           _bitset?._duplicate?, ~ _holder_1, ~ _holder_2
    arrange         _holder_1, _result.=transition?
    arrange         _transition, _machine.=transition?
    _call           _bitset?._duplicate?, ~ _holder_1, ~ _transition
    _table          _result
    _bitset_foreach _transition, _item
      arrange       _holder_1, _result.=table?._item?
      arrange       _holder_2, _machine.=table?._item?
      _call         _transition_meta_duplicate?, ~ _holder_1, ~ _holder_2
    _end            _foreach
  end calminstruction

  calminstruction _destroy? _result?*
    local           _holder, _item, _meta
    arrange         _holder, _result.=accept?
    _call           _bitset?._destroy?, ~ _holder
    arrange         _holder, _result.=transition?
    _bitset_foreach _holder, _item
      arrange       _meta, _result.=table?._item?
      _call         _transition_meta_destroy, ~ _meta
    _end            _foreach
    _call           _bitset?._destroy?, ~ _holder
    restore         _result.=start?, _result.=stcnt?, _result.=table?
  end calminstruction

  calminstruction _empty? _result?*, _machine?*
    arrange     _machine, _machine.=states?
    _call       _bitset?._empty?, ~ _result, ~ _machine
  end calminstruction

  calminstruction _adjust? _result?*, _threshold?*
    local               _value, _holder_1, _holder_2, _container, _item, _base,\
                          _target, _position, _index, _limit, _transition
    varrfsh             _threshold
    cmpz                _threshold
    jyes                _adjust_finish
    arrange             _value, _result.=start?
    add                 _value, _threshold
    assign              _result.=start?, _value
    arrange             _value, _result.=stcnt?
    add                 _value, _threshold
    assign              _result.=stcnt?, _value
    arrange             _container, _result.=states?
    _bitset_foreach     _container, _item
      add               _item, _threshold
    _end                _foreach
    arrange             _container, _result.=accept?
    _bitset_foreach     _container, _item
      add               _item, _threshold
    _end                _foreach
    arrange             _container, _result.=transition?
    _bitset_foreach     reverse _container, _item
      compute           _position, (_item + _threshold)
      arrange           _base, _result.=table?._item?
      arrange           _holder_2, _base.=epsilon?
      _bitset_foreach   _holder_2, _target
        add             _target, _threshold
      _end              _foreach
      symrfsh           _position
      arrange           _holder_1, _result.=table?._position?.=epsilon?
      call              _bitset?._duplicate?, _holder_1, _holder_2
      arrange           _limit, _base.=trcnt?
      varrfsh           _limit
      assign            _result.=table?._position?.=trcnt?, _limit
      setz              _index
     _adjust_loop:
      check             (_index < _limit)
      jno               _adjust_shift
      symrfsh           _index
      arrange           _transition, _base.=destination?._index?
      add               _transition, _threshold
      assign            _result.=table?._position?.=destination?._index?, _transition
      arrange           _holder_1, _result.=table?._position?.=charset?._index?
      arrange           _holder_2, _base.=charset?._index?
      call              _bitset?._duplicate?, _holder_1, _holder_2
      inc               _index
      jump              _adjust_loop
     _adjust_shift:
      add               _item, _threshold
      call              _transition_meta_destroy, _base
    _end                _foreach
   _adjust_finish:
  end calminstruction

  calminstruction _transition? _result?*, _state_1?*, _condition?, _state_2?*
    local       _return, _holder, _value, _index, _tested, _update, _min, _max, _charset, _epsilon, _lookup, _meta
    setz        _update
    _balance    _state_1, {}
    jno         _transition_finish
    _balance    _state_2, {}
    jno         _transition_finish
    reprnum     _state_1
    reprnum     _state_2
    arrange     _holder, _result.=states?
    arrange     _lookup, {_state_1}
    _call       _bitset?._member?, _return, ~ _holder, ~ _lookup
    cmpz        _return
    jyes        _transition_finish
    arrange     _lookup, {_state_2}
    _call       _bitset?._member?, * _return, ~ _holder, ~ _lookup
    cmpz        _return
    jyes        _transition_finish
    arrange     _epsilon, _result.=table?._state_1?.=epsilon?
    arrange     _holder, _result.=transition?
    arrange     _lookup, {_state_1}
    _call       _bitset?._member?, * _return, ~ _holder, ~ _lookup
    cmpz        _return
    jno         _transition_insert
    arrange     _meta, _result.=table?._state_1?
    _call       _transition_meta?, ~ _meta, ~ _constant?._zero?
    not         _update
   _transition_insert:
    _call       _bitset?._insert?, ~ _holder, ~ _lookup
    symrfsh     _condition
    match       ,_condition
    jyes        _transition_epsilon
    arrange     _value, _result.=table?._state_1?.=trcnt?
    reprnum     _value
    cmpz        _update
    jno         _transition_assign
    setz        _index
   _transition_search:
    check       (_index < _value)
    jno         _transition_mark
    arrange     _tested, _result.=table?._state_1?.=destination?._index?
    varrfsh     _tested
    cmp         _tested, _state_2
    jyes        _transition_found
    inc         _index
    jump        _transition_search
   _transition_found:
    arrange     _value, _index
    jump        _transition_charset
   _transition_mark:
    not         _update
   _transition_assign:
    assign      _result.=table?._state_1?.=destination?._value?, _state_2
    arrange     _holder, _result.=table?._state_1?.=charset?._value?
    _call       _bitset?._declare?, ~ _holder
   _transition_charset:
    arrange     _charset, _result.=table?._state_1?.=charset?._value?
    cmpz        _update
    jyes        _transition_parse
    inc         _value
    assign      _result.=table?._state_1?.=trcnt?, _value
   _transition_parse:
    match       _min?=-_max?, _condition
    jno         _transition_update
    match       ,_min
    jno         _transition_sanitize
    setz        _min
   _transition_sanitize:
    match       ,_max
    jno         _transition_ensure
    compute     _max, _constant?._byte_mask?
   _transition_ensure:
    _asmcmd     =assert ((_min) <== (_max))
    and         _min, _constant?._byte_mask?
    and         _max, _constant?._byte_mask?
   _transition_loop:
    check       (_min < _max)
    compute     _condition, _min
    jno         _transition_update
    arrange     _lookup, {_min}
    _call       _bitset?._insert?, ~ _charset, ~ _lookup
    inc         _min
    jump        _transition_loop
   _transition_update:
    and         _condition, _constant?._byte_mask?
    arrange     _lookup, {_condition}
    _call       _bitset?._insert?, ~ _charset, ~ _lookup
    jump        _transition_finish
   _transition_epsilon:
    arrange     _lookup, {_state_2}
    _call       _bitset?._insert?, ~ _epsilon, ~ _lookup
   _transition_finish:
  end calminstruction

  calminstruction _merge? _result?*, _machine?*, _include?*
    local               _holder_1, _holder_2, _lookup_1, _lookup_2, _charset, _character,\
                            _diagram, _item, _index, _limit, _out, _epsilon
    _asmcmd             =assert (_machine.=stcnt? > _result.=stcnt?)
    movvar              _result.=stcnt?, _machine.=stcnt?
    arrange             _holder_1, _result.=states?
    arrange             _holder_2, _machine.=states?
    _call               _bitset?._union?, ~ _holder_1, ~ _holder_2
    varrfsh             _include
    cmpz                _include
    jyes                _merge_foreach
    arrange             _holder_1, _result.=accept?
    arrange             _holder_2, _machine.=accept?
    _call               _bitset?._union?, ~ _holder_1, ~ _holder_2
   _merge_foreach:
    arrange             _diagram, _machine.=transition?
    _bitset_foreach     _diagram, _item
      reprnum           _item
      arrange           _lookup_1, {_item}
      arrange           _limit, _machine.=table?._item?.=trcnt?
      varrfsh           _limit
      setz              _index
     _merge_loop:
      check             (_index < _limit)
      jno               _merge_epsilon
      arrange           _out, _machine.=table?._item?.=destination?._index?
      reprnum           _out
      arrange           _lookup_2, {_out}
      arrange           _charset, _machine.=table?._item?.=charset?._index?
      _bitset_foreach   _charset, _character
        symrfsh         _character
        _call           _transition, ~ _result, ~ _lookup_1, ~ _character, ~ _lookup_2
      _end              _foreach
      inc               _index
      jump              _merge_loop
     _merge_epsilon:
      arrange           _epsilon, _machine.=table?._item?.=epsilon?
      _bitset_foreach   _epsilon, _out
        reprnum         _out
        arrange         _lookup_2, {_out}
        _call           _transition, ~ _result, ~ _lookup_1, ~ _constant?._empty?, ~ _lookup_2
      _end              _foreach
    _end                _foreach
  end calminstruction

  calminstruction _new_state? _result?*, _start?*, _final?*, _retreive?
    local       _return, _holder, _increment, _state, _lookup
    arrange     _state, _result.=stcnt?
    varrfsh     _state
    match       ,_retreive
    jyes        _new_state_update
    publish     _retreive, _state
   _new_state_update:
    compute     _increment, (_state + 1H)
    assign      _result.=stcnt?, _increment
    varrfsh     _start
    varrfsh     _final
    arrange     _holder, _result.=states?
    arrange     _lookup, {_state}
    _call       _bitset?._member?, _return, ~ _holder, ~ _lookup
    cmpz        _return
    jno         _new_state_finish
    _call        _bitset?._insert?, ~ _holder, ~ _lookup
    cmpz        _start
    jyes        _new_state_accept
    assign      _result.=start?, _state
   _new_state_accept:
    cmpz        _final
    jyes        _new_state_finish
    arrange     _holder, _result.=accept?
    _call       _bitset?._insert?, ~ _holder, ~ _lookup
   _new_state_finish:
  end calminstruction

  calminstruction _skeleton? _result?*
    call        _declare, _result
    call        _new_state, _result, _constant?._true?, _constant._false?, _constant._empty?
    call        _new_state, _result, _constant?._false?, _constant._true?, _constant._empty?
  end calminstruction

  calminstruction _thompson_form? _result?*, _machines?*&
    local       _value, _machine, _holder, _start, _return, _lookup
    _cstwrp     _value
    setz        _return
    _iterate    _machine, _machines
      arrange   _holder, _machine.=accept?
      call      _bitset?._length?, __value, _holder
      cmp       _value, 1H
      jno       _thompson_form_publish
      arrange   _start, _machine.=start?
      varrfsh   _start
      cmpz      _start
      jno       _thompson_form_publish
      arrange   _holder, _machine.=accept?
      arrange   _lookup, {_start}
      call      _bitset?._member?, __value, _holder, _lookup
      cmpz      _value
      jno       _thompson_form_publish
    _end        _iterate
    not         _return
   _thompson_form_publish:
    publish     _result, _return
  end calminstruction

  macro calminstruction?._sanitize? _check?*, _return?*, _label_1?*, _label_2?*, _machines?*&
    cmpz        _check
    jyes        _label_1
    _call       _thompson_form, _return, ~ _machines
    cmpz        _return
    jyes        _label_2
  end macro

  calminstruction _thompson_concat? _result?*, _machine?*, _check?:0H
    local       _return, _value, _temporary
    _sanitize   _check, _return, _thompson_concat_perform, _thompson_concat_finish, _result, _machine
   _thompson_concat_perform:
    _call       _unique, _temporary, concat
    _call       _duplicate, ~ _temporary, ~ _machine
    arrange     _value, _result.=stcnt?
    dec         _value
    _call       _adjust, ~ _temporary, ~ _value
    _call       _merge, ~ _result, ~ _temporary, ~ _constant?._false?
    arrange     _result, _result.=accept?
    arrange     _value, _temporary.=accept?
    _call       _bitset?._duplicate?, ~ _result, ~ _value
    _call       _destroy, ~ _temporary
   _thompson_concat_finish:
  end calminstruction

  calminstruction _thompson_union? _result?*, _machine?*, _check?:0H
    local       _return, _holder, _lookup_1, _lookup_2, _temporary, _value, _final_1, _final_2, _finish
    _sanitize   _check, _return, _thompson_union_perform, _thompson_union_finish, _result, _machine
  _thompson_union_perform:
    compute     _value, 1H
    _call       _adjust, ~ _result, ~ _value
    _call       _unique, _temporary, union
    _call       _duplicate, ~ _temporary, ~ _machine
    arrange     _value, _result.=stcnt?
    varrfsh     _value
    _call       _adjust, ~ _temporary, ~ _value
    setz        _value
    assign      _result.=start?, _value
    arrange     _holder, _result.=states?
    arrange     _lookup_1, {0H}
    _call       _bitset?._insert?, ~ _holder, ~ _lookup_1
    _call       _merge, ~ _result, ~ _temporary, ~ _constant?._false?
    arrange     _lookup_2, {1H}
    _call       _transition, ~ _result, ~ _lookup_1, ~ _constant?._empty?, ~ _lookup_2
    arrange     _value, _temporary.=start?
    varrfsh     _value
    arrange     _lookup_2, {_value}
    _call       _transition, ~ _result, ~ _lookup_1, ~ _constant?._empty?, ~ _lookup_2
    arrange     _holder, _result.=accept?
    _call       _bitset?._element?, _final_1, ~ _holder, ~ _constant?._zero?
    arrange     _holder, _temporary.=accept?
    _call       _bitset?._element?, _final_2, ~ _holder, ~ _constant?._zero?
    reprnum     _final_1
    reprnum     _final_2
    arrange     _holder, _result.=accept?
    _call       _bitset?._declare?, ~ _holder
    _call       _new_state, ~ _result, ~ _constant?._false?, ~ _constant?._true?, _finish
    reprnum     _finish
    arrange     _lookup_1, {_final_1}
    arrange     _lookup_2, {_finish}
    _call       _transition, ~ _result, ~ _lookup_1, ~ _constant?._empty?, ~ _lookup_2
    arrange     _lookup_1, {_final_2}
    _call       _transition, ~ _result, ~ _lookup_1, ~ _constant?._empty?, ~ _lookup_2
    _call       _destroy, ~ _temporary
   _thompson_union_finish:
  end calminstruction

  calminstruction _thompson_closure? _result?*, _check?:0H
    local       _value, _lookup_1, _lookup_2, _holder, _final, _retreive
    _sanitize   _check, _return, _thompson_closure_perform, _thompson_closure_finish, _result
   _thompson_closure_perform:
    compute     _value, 1H
    _call       _adjust, ~ _result, ~ _value
    arrange     _holder, _result.=accept?
    _call       _bitset?._element?, _final, ~ _holder, ~ _constant?._zero?
    varrfsh     _final
    arrange     _lookup_1, {_final}
    arrange     _lookup_2, {1H}
    _call       _transition, ~ _result, ~ _lookup_1, ~ _constant?._empty?, ~ _lookup_2
    arrange     _lookup_1, {0H}
    arrange     _holder, _result.=states?
    _call       _bitset?._insert?, ~ _holder, ~ _lookup_1
    _call       _transition, ~ _result, ~ _lookup_1, ~ _constant?._empty?, ~ _lookup_2    
    arrange     _holder, _result.=accept?
    _call       _bitset?._declare?, ~ _holder
    _call       _new_state, ~ _result, ~ _constant?._false?, ~ _constant?._true?, _retreive
    varrfsh     _retreive
    arrange     _lookup_1, {_final}
    arrange     _lookup_2, {_retreive}
    _call       _transition, ~ _result, ~ _lookup_1, ~ _constant?._empty?, ~ _lookup_2
    arrange     _lookup_1, {0H}
    _call       _transition, ~ _result, ~ _lookup_1, ~ _constant?._empty?, ~ _lookup_2
    setz        _retreive
    assign      _result.=start?, _retreive
   _thompson_closure_finish:
  end calminstruction

  ; A+ => AA*
  calminstruction _emulate_positive? _result?*
    local       _temporary
    _call       _unique, _temporary, positive
    _call       _duplicate, ~ _temporary, ~ _result
    _call       _thompson_closure, ~ _temporary
    _call       _thompson_concat, ~ _result, ~ _temporary
    _call       _destroy, ~ _temporary
  end calminstruction

  ; A? => A|
  calminstruction _emulate_optional? _result?*
    local       _temporary
    _init       const _lookup_1, {0H}
    _init       const _lookup_2, {1H}
    _call       _unique, _temporary, optional
    _call       _skeleton, ~ _temporary
    _call       _transition, ~ _temporary, ~ _lookup_1, ~ _constant?._empty?, ~ _lookup_2
    _call       _thompson_union, ~ _result, ~ _temporary  
    _call       _destroy, ~ _temporary
  end calminstruction

  ; A{N}   => A...A (N times)
  ; A{N,M} => A...A | A...A | ... (N * M times)
  calminstruction _finite_sequence?: _result?*, _arg1?*, _arg2?
    local       _temporary, _destination, _holder, _origin, _index, _min, _max
    take        _min, _arg1
    take        _max, _arg2
    take        _destination, _result
    _call       _unique, _temporary, finite
    take        _origin, _temporary
    call        _duplicate, _origin, _destination
    _call       _unique, * _temporary, * finite
    take        _holder, _temporary
    execute     { assert (_min >= 0H) }
    match       ,_max
    jyes        _finite_sequence_concat
    execute     { assert (_max >= _min) }
    cmp         _max, _min
    jyes        _finite_sequence_concat
    _call       _finite_sequence, ~ _destination, ~ _min, ~ _constant?._empty?
    push        _index, _min
    inc         _index
   _finite_sequence_union_loop:
    check       (_index <= _max)
    jno         _finite_sequence_finish
    _call       _duplicate, ~ _holder, ~ _origin
    _call       _finite_sequence, ~ _holder, ~ _index, ~ _constant?._empty?
    _call       _thompson_union, ~ _destination, ~ _holder
    _call       _destroy, ~ _holder
    inc         _index
    jump        _finite_sequence_union_loop
   _finite_sequence_concat:
    cmpz        _min
    jno         _finite_sequence_positive
    _call       _destroy, ~ _destination
    _call       _declare, ~ _destination
    jump        _finite_sequence_finish
   _finite_sequence_positive:
    push        _index, 0H
    dec         _min
   _finite_sequence_concat_loop:
    check       (_index < _min)
    jno         _finite_sequence_finish
    _call       _thompson_concat, ~ _destination, ~ _origin
    inc         _index
    jump        _finite_sequence_concat_loop
   _finite_sequence_finish:
    _call       _destroy, ~ _origin
    pop         _destination, _holder, _origin, _index, _min, _max
  end calminstruction

  ; A{N,} => (A...A)A* (N times)
  calminstruction _infinite_sequence? _result?*, _base?*
    local       _temporary
    _call       _unique, _temporary, infinite
    _call       _duplicate, ~ _temporary, ~ _result
    _call       _thompson_closure, ~ _temporary
    _call       _finite_sequence, ~ _result, ~ _base, ~ _constant?._empty?
    _call       _thompson_concat, ~ _result, ~ _temporary
    _call       _destroy, ~ _temporary
  end calminstruction

  calminstruction _delta? _result?*, _base?*, _machine?*, _character?*
    local           _item, _out, _return, _holder, _lookup, _index, _limit, _temporary
    _call           _unique, _temporary, delta
    _call           _bitset?._blit?, ~ _temporary, ~ _base
    _call           _bitset?._declare?, ~ _result
    varrfsh         _character
    _bitset_foreach _temporary, _item
      arrange       _holder, _machine.=transition?
      arrange       _lookup, {_item}
      _call         _bitset?._member?, _return, ~ _holder, ~ _lookup
      cmpz          _return
      _jyesnext
      setz          _index
      arrange       _limit, _machine.=table?._item?.=trcnt?
      varrfsh       _limit
     _delta_loop:
      check         (_index < _limit) 
      _jnonext
      arrange       _holder, _machine.=table?._item?.=charset?._index?
      arrange       _lookup, {_character}
      _call         _bitset?._member?, * _return, ~ _holder, ~ _lookup
      cmpz          _return
      jyes          _delta_next
      arrange       _out, _machine.=table?._item?.=destination?._index?
      varrfsh       _out
      arrange       _lookup, {_out}
      _call         _bitset?._insert?, ~ _result, ~ _lookup
     _delta_next:
      inc           _index
      jump          _delta_loop
    _end            _foreach
    _call           _bitset?._destroy?, ~ _temporary
  end calminstruction

  calminstruction _epsilon_closure? _result?*, _base?*, _machine?*
    local           _temporary, _holder, _lookup, _return, _target, _item
    _call           _bitset?._blit?, ~ _result, ~ _base
    _call           _unique, _temporary, epsilon
    _call           _bitset?._duplicate?, ~ _temporary, ~ _result
   _epsilon_closure_loop:
    _bitset_foreach _result, _item
      arrange       _holder, _machine.=transition?
      arrange       _lookup, {_item}
      _call         _bitset?._member?, _return, ~ _holder, ~ _lookup
      cmpz          _return
      _jyesnext
      arrange       _holder, _machine.=table?._item?.=epsilon?
      _call         _bitset?._union?, ~ _temporary, ~ _holder
    _end            _foreach
    _call           _bitset?._equivalent?, * _return, ~ _temporary, ~ _result
    cmpz            _return
    jno             _epsilon_closure_finish
    _call           _bitset?._union?, ~ _result, ~ _temporary
    jump            _epsilon_closure_loop
   _epsilon_closure_finish:
    _call           _bitset?._destroy?, ~ _temporary
  end calminstruction

  calminstruction _connect? _result?*, _machines?*&
    local       _temporary, _holder, _lookup_1, _lookup_2, _value, _machine
    _call       _unique, _temporary, connect
    compute     _value, 1H
    _call       _adjust, ~ _result, ~ _value
    setz         _value
    assign      _result.=start?, _value
    arrange     _holder, _result.=states?
    arrange     _lookup_1, {0H}
    _call       _bitset?._insert?, ~ _holder, ~ _lookup_1
    arrange     _lookup_2, {1H}
    _call       _transition, ~ _result, ~ _lookup_1, ~ _constant?._empty?, ~ _lookup_2
    evaluate    _value, _result.=stcnt?
    _iterate    _machine, _machines
      _call     _duplicate, ~ _temporary, ~ _machine
      _call     _adjust, ~ _temporary, ~ _value
      _call     _merge, ~ _result, ~ _temporary, ~ _constant?._true?
      arrange   _lookup_2, {_value}
      _call     _transition, ~ _result, ~ _lookup_1, ~ _constant?._empty?, ~ _lookup_2
      evaluate  _value, _temporary.=stcnt?
      _call     _destroy, ~ _temporary
    _end        _iterate
  end calminstruction

  calminstruction _subset_construction? _result?*, _machine?*
    local       _return, _temporary, _match, _holder, _lookup, _empty, _unvisit, _stack,\
                  _storage, _symbol, _current, _found, _index, _total, _accept
    local       _value

    _cstwrp     _return
    _cstwrp     _temporary
    _cstwrp     _match
    _cstwrp     _found
    _cstwrp     _empty
    _cstwrp     subset
    _init       var const _position, 0H
    _init       var const _byte, 100H
    call        _unique, __match, _subset
    call        _unique, __return, _subset
    publish     _result, _return
    _virtual    _return
    _asmcmd     .=_state_table:
    ;_repeat     100H, _symbol:0H
    ;  _asmcmd   =db 0H
    ;_end        _repeat

    arrange     _holder, _machine.=accept?
    call        _unique, __empty, _subset
    call        _bitset?._declare?, _empty
    take        _stack, _empty
    call        _unique, __temporary, _subset
    arrange     _value, _machine.=start?
    varrfsh     _value    
    arrange     _lookup, {_value}
    call        _epsilon_closure, _temporary, _lookup, _machine
    push        _unvisit, _temporary
    push        _stack, _temporary
    compute     _total, 2H
   _subset_construction_until:
    take        _unvisit,_unvisit
    jno         _subset_construction_finish
    ;_asmcmd     =db 00AH, "db "
    take        _current, _unvisit
    _repeat     _byte, _symbol:0H
      ;symrfsh  _symbol
      call      _unique, __temporary, _subset
      call      _delta, _temporary, _current, _machine, _symbol
      call      _epsilon_closure, _temporary, _temporary, _machine
      setz      _found
      setz      _index
     _subset_construction_mark:
      take      _storage, _stack
      jno       _subset_construction_restore
      call      _bitset?._equivalent?, __return, _temporary, _storage
      inc       _found
      cmpz      _return
      jyes      _subset_construction_mark
      not       _index
     _subset_construction_restore:
      take      _stack, _storage
      jyes      _subset_construction_restore
      compute   _found, (_total - _found)
      cmpz      _index
      jno       _subset_construction_increment
      queue     _unvisit, _temporary
      push      _stack, _temporary
      inc       _total
      compute   _found, (_total - 1H)
      call      _bitset?._duplicate?, _match, _temporary
      call      _bitset?._intersection?, _match, _holder
      call      _bitset?._empty?, __return, _match
      cmpz      _return
      jno       _subset_construction_increment
      call      _bitset?._element?, __return, _match, _position
      push      _accept, _found,_return
     _subset_construction_increment:
      ;symrfsh   _found
      ;stringify _found
      _asmcmd   =db _found
      cmp       _symbol, 0FFH
      _jyesexit
      ;_asmcmd   =db ","
    _end        _repeat
    jump        _subset_construction_until
   _subset_construction_finish:
    _asmcmd     .=_state_table.=sizeof == (=$ - .=_state_table)
    _asmcmd     .=_accept_table:
   _subset_construction_unroll:
    take        _accept,_accept
    jno         _subset_construction_end
    _asmcmd     =dd _accept
    ;arrange     _found, _accept
    ;stringify   _found
    ;;_asmcmd     =db "db ", __found, ", 0", 00AH
    take        ,_accept
    jump        _subset_construction_unroll
   _subset_construction_end:
    _asmcmd     .=_accept_table.=sizeof == (=$ - .=_accept_table)
    _asmcmd     =end =virtual
  end calminstruction

  calminstruction _display_character_transition? _byte?*
    local       _value
    compute     _value, (_byte and 00FH)
    and         _byte, 0F0H
    shr         _byte, 4H
    _call       _cvthex, _value, ~ _value
    _call       _cvthex, _byte, ~ _byte
    compute     _byte, string("0x" or (_byte shl 018H) or (_value shl 020H))
    execute     { display _byte }
  end calminstruction

  calminstruction _display? _result?*
    local               _start, _holder, _transition, _epsilon, _target, _charset, _item, _index,\
                            _limit, _out, _character, _first, _last_1, _last_2
    execute             { display "START<" }
    arrange             _start, _result.=start?
    reprnum             _start
    stringify           _start
    execute             { display _start, ">", 00AH }
    execute             { display "STATES:" }
    arrange             _holder, _result.=states?
    _call               _bitset?._display?, ~ _holder
    execute             { display "FINAL:" }
    arrange             _holder, _result.=accept?
    _call               _bitset?._display?, ~ _holder
    execute             { display "TRANSITION:{" }
    arrange             _transition, _result.=transition?
    _bitset_foreach     _transition, _item, _first, _last_1
      arrange           _start, _item
      stringify         _start
      arrange           _epsilon, _result.=table?._item?.=epsilon?
      _bitset_foreach   _epsilon, _target,,
        arrange         _out, _target
        reprnum         _out
        stringify       _out
        execute         { display "delta(", _start, ",EPSILON,", _out, ")" }
      _end              _foreach
      setz              _index
      arrange           _limit, _result.=table?._item?.=trcnt?
      varrfsh           _limit
     _display_loop:
      check             (_index < _limit)
      _jnonext
      arrange           _out, _result.=table?._item?.=destination?._index?
      reprnum           _out
      stringify         _out
      arrange           _charset, _result.=table?._item?.=charset?._index?
        _bitset_foreach _charset, _character,, _last_2
          execute       { display "delta(", _start, "," }
          _call         _display_character_transition, _character
          execute       { display ",", _out, ")" }
          cmpz          _last_2
          _jnoexit
          execute       { display "," }
        _end            _foreach
      ;check             ((_index = 0H) & (_first <> 0H))
      inc               _index
      ;jyes              _display_loop
      ;execute           { display "," }
      jump              _display_loop
    _end                _foreach
   _display_finish:
    execute             { display "}", 00AH }
  end calminstruction
end namespace

