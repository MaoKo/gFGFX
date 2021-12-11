
;struc _nonterminal? _productions?, _nullable?*, _discard?*, _optional?*, _list?*, _cache?*, _hash?*
;   define .exists?
;   .replacement?
;   .productions? = _productions
;   .nullable? = _nullable
;   .discard? = _discard
;   .optional? = _optional
;   .list? = _list
;   .cache? = _cache
;   .hash? = _hash
;end struc

;struc _production? _hash?*, _count?*, _cnflnter?*, _cnfrnter?*, _cnfterm?*, _first?*
;   .hash? = _hash
;   .count? = _count
;   .cnflnter? = _cnflnter
;   .cnfrnter? = _cnfrnter
;   .cnfterm? = _cnfterm
;   .first? _bitset _first
;end struc

_parser? := 0H
namespace _parser?
  virtual at 0H
    include "parser.lex.inc"
  end virtual

  calminstruction _nonterminal_declare? _result?*, _symbol?*
    restore     _result.=exist?
    assign      _result.=exist?, _constant?._empty?
    assign      _result.=replacement?, _constant?._empty?
    assign      _result.=productions?, _constant?._zero?
    assign      _result.=nullable?, _constant?._zero?
    assign      _result.=discard?, _constant?._zero?
    assign      _result.=optional?, _constant?._zero?
    assign      _result.=list?, _constant?._zero?
    ;assign     _result.=reach?, _constant?._zero?
    assign      _result.=cache?, _constant?._zero?
    stringify   _symbol
    reprnum     _symbol
    assign      _result.=hash?, _symbol
  end calminstruction

  calminstruction _production_declare? _result?*, _hash?*, _count?*
    local     _holder
    assign    _result.=hash?, _hash
    assign    _result.=count?, _count
    assign    _result.=cnflnter?, _constant?._empty?
    assign    _result.=cnfrnter?, _constant?._empty?
    assign    _result.=cnfterm?, _constant?._empty?
    arrange   _holder, _result.=first?
    call      _bitset?._declare?, _holder
  end calminstruction

  calminstruction _production_duplicate? _result?*, _target?*
    ;movsym        _result.=nonterminal?._target._index_1?, _result.=nonterminal?._target._index_2?
    ;movsym  _result.=nonterminal?._target._index_1?.=hash?, _result.=nonterminal?._target._index_2?.=hash?
    movvar  _result.=count?, _target.=count?
    ;move          _result.=nonterminal?._target._index_1?.=cnflnter?, _result.=nonterminal?._target._index_2?.=cnflnter?
    ;move          _result.=nonterminal?._target._index_1?.=cnfrnter?, _result.=nonterminal?._target._index_2?.=cnfrnter?
    ;move          _result.=nonterminal?._target._index_1?.=cnfterm?, _result.=nonterminal?._target._index_2?.=cnfterm?
  end calminstruction

  calminstruction _production_destroy? _result?*
    restore   _result.=hash?, _result.=count?, _result.=cnflnter?, _result.=cnfrnter?, _result.=cnfterm?
  end calminstruction

  calminstruction _declare? _result?*
    assign      _result.=nonterminal?, _constant?._zero?
    assign      _result.=record?, _constant?._empty?
    assign      _result.=start?, _constant?._empty?
    assign      _result.=index?, _constant?._zero?
  end calminstruction

  calminstruction _dupnter? _result?*, _target?*
    local       _holder, _count, _index
    evaluate    _holder, _target.=productions?
    compute     _count, _holder
    assign      _result.=productions?, _holder
    _repeat     _count, _index:0H
      expand    _holder, _target._index?
      assign    _result._index?, _holder
    _end        _repeat
    evaluate    _holder, _target.=optional?
    assign      _result.=optional?, _holder
    evaluate    _holder, _target.=list?
    assign      _result.=list?, _holder
    expand      _holder, _target.=hash?
    assign      _result.=hash?, _holder
    expand      _holder, _target.=replacement?
    assign      _result.=replacement?, _holder
  end calminstruction

  calminstruction _duplicate? _result?*, _parser?*
    local       _holder, _symbol, _copy_1, _copy_2
    _init       var const _zero, 0H
    assign      _result.=nonterminal?, _zero
    expand      _holder, _parser.=start?
    assign      _result.=start?, _holder
    expand      _holder, _parser.=record?
    assign      _result.=record?, _holder
    _iterate    _symbol*, _holder
      arrange   _copy_1, _result.=nonterminal?._symbol
      arrange   _copy_2, _parser.=nonterminal?._symbol
      call      _dupnter, _copy_1, _copy_2
    _end        _iterate
  end calminstruction

  calminstruction _nonterminal? _result?*, _start?*, _symbol?*&
    local           _holder, _index
    match           =<_symbol=>, _symbol
    jno             _nonterminal_finish
    _transformable  _result.=nonterminal?._symbol.=exist?
    jyes            _nonterminal_finish
    expand          _holder, _result.=record?
    match           ,_holder
    jno             _nonterminal_append
    arrange         _holder, _symbol
    jump            _nonterminal_update
   _nonterminal_append:
    arrange         _holder, _holder,_symbol
   _nonterminal_update:
    assign          _result.=record?, _holder    
    varrfsh         _start
    cmpz            _start
    jyes            _nonterminal_register
    assign          _result.=start?, _symbol
   _nonterminal_register:
    evaluate        _index, _result.=index?
    arrange         _holder, _result.=nonterminal?._symbol
    assign          _holder, _index
    inc             _index
    assign          _result.=index?, _index
    _call           _nonterminal_declare, ~ _holder, ~ _symbol
   _nonterminal_finish:
  end calminstruction

  calminstruction _productions? _result?*, _productions?*&
    local               _lhs, _reason, _rhs, _holder, _symbol, _increment, _hash, _compare, _cterm, _cnter,\
                            _left, _right, _count, _declare
    _cstwrp             _symbol
    _init               const _badsyms, "parser: unknown symbol `", __symbol, "`"
    _init               const _badnter, "parser: nonterminal unknown `", __symbol, "`"
    match               _lhs -> _productions?, _productions
    jno                 _productions_finish
    match               =<_lhs=>, _lhs
    jno                 _productions_finish
    _transformable      _result.=nonterminal?._lhs.=exist?
    jno                 _productions_finish
    arrange             _holder, _result.=nonterminal?._lhs.=productions?
    compute             _increment, _holder
    _iterate            _rhs, _productions, |
      setz              _cterm
      setz              _cnter
      arrange           _hash,
      setz              _count
      match             ,_rhs
      jyes              _prodcutions_assign
      _iterate          _symbol, _rhs
        inc             _count
        match           =<_symbol=>, _symbol
        jyes            _productions_nonterminal
        match           =(_symbol=), _symbol
        jyes            _productions_terminal
        arrange         _reason, _badsyms
       _productions_error:
        stringify       _symbol
        _asmcmd         =err _reason
        jump            _productions_finish
       _productions_nonterminal:
        inc             _cnter
        arrange         _reason, _badnter
        _transformable  _result.=nonterminal?._symbol.=exist?
        jno             _productions_error
        arrange         _hash, _hash,<_symbol>
        _continue
       _productions_terminal:
        inc             _cterm
        varrfsh         _symbol
        arrange         _hash, _hash,_symbol
      _end              _iterate
     _prodcutions_assign:
      _delcma           _hash
      stringify         _hash
      reprnum           _hash
      _repeat           _increment, _index:_constant?._false?
        evaluate        _compare, _result.=nonterminal?._lhs._index?.=hash?
        cmp             _hash, _compare
        jyes            _productions_continue
      _end              _repeat
      arrange           _declare, _result.=nonterminal?._lhs._increment?
      publish           _declare, _rhs
      _call             _production_declare, ~ _declare, ~ _hash, ~ _count
      check             ((_count = 2H) & (_cnter = 2H))
      jno               _productions_alone
      match             =<_left=>=,=<_right=>, _rhs
      evaluate          _left, _result.=nonterminal?._left
      evaluate          _right, _result.=nonterminal?._right
      assign            _result.=nonterminal?._lhs._increment?.=cnflnter?, _left
      assign            _result.=nonterminal?._lhs._increment?.=cnfrnter?, _right
      jump              _productions_update
     _productions_alone:
      check             ((_count = 1H) & (_cterm = 1H))
      jno               _productions_update
      match             =(_rhs=), _rhs
      varrfsh           _rhs
      assign            _result.=nonterminal?._lhs._increment?.=cnfterm?, _rhs
     _productions_update:
      inc               _increment
     _productions_continue:
    _end                _iterate
    publish             _holder, _increment
   _productions_finish:
  end calminstruction

  calminstruction _mark_first? _result?*
    local           _holder, _symbol, _count, _bitset, _head, _remain, _change, _target,\
                        _union, _insert, _temporary, _return, _null, _glassy
    _unique         _temporary, _first
    expand          _holder, _result.=record?
    _iterate        _symbol*, _holder
      evaluate      _count, _result.=nonterminal?._symbol.=productions?
      _repeat       _count, _index:_constant?._zero?
        arrange     _bitset, _result.=nonterminal?._symbol._index?.=first?
        _call       _bitset?._declare?, _bitset
      _end          _repeat
    _end            _iterate
    call            _mark_nullable?, _result
   _mark_first_loop:
    setz            _change
    _iterate        _symbol*, _holder
      evaluate      _count, _result.=nonterminal?._symbol.=productions?
      _repeat       _count, _index:_constant?._zero?
        setz        _glassy
        arrange     _bitset, _result.=nonterminal?._symbol._index?.=first?
        _call       _bitset?._declare?, ~ _temporary
        expand      _head, _result.=nonterminal?._symbol._index?
       _mark_first_scan:
        match       =(_head=) _remain?, _head
        jyes        _mark_first_terminal    
        match       =<_head=> _remain?, _head
        _jnonext
        inc         _glassy
        evaluate    _target, _result.=nonterminal?._head.=productions?
        _repeat     _target, _insert:_constant?._zero?
          arrange   _union, _result.=nonterminal?._head._insert?.=first?
          _call     _bitset?._union?, ~ _temporary, ~ _union
        _end        _repeat
        evaluate    _null, _result.=nonterminal?._head.=nullable?
        arrange     _head, _remain
        _delcma     _head
        cmpz        _null
        jno         _mark_first_scan 
       _mark_first_subset:
        _incsub     _return, __return, _bitset, _temporary, _jnonext, jump _mark_first_update
       _mark_first_terminal:
        varrfsh     _head
        arrange     _head, {_head}
        _call       _bitset?._member?, _return, ~ _bitset, ~ _head
        _call       _bitset?._insert?, ~ _temporary, ~ _head
        cmpz        _glassy
        jno         _mark_first_subset
        cmpz        _return
        _jnonext
        _call       _bitset?._insert?, ~ _bitset, ~ _head
       _mark_first_update:
        inc         _change
      _end          _repeat
    _end            _iterate
    cmpz            _change
    jno             _mark_first_loop
    _call           _bitset?._destroy?, ~ _temporary
  end calminstruction

  calminstruction _first? _result?*, _parser?*, _target?*&
    local           _count, _bitset, _defined
    match           =<_target=>, _target
    jno             _first_finish
    _transformable  _result.=nonterminal?._target.=exist?
    jno             _first_finish
    _call           _mark_first, ~ _parser
    _call           _bitset?._declare?, ~ _result
    evaluate        _count, _parser.=nonterminal?._target.=productions?
    _repeat         _count, _index:_constant?._zero?
      arrange       _bitset, _parser.=nonterminal?._target._index?.=first?
      _call         _bitset?._union?, ~ _result, ~ _bitset
    _end            _repeat
   _first_finish:
  end calminstruction

  calminstruction _follow?: _result?*, _parser?*, _target?*&
    local           _holder, _destination, _self, _control, _temporary, _bitset, _return, _symbol,\
                        _change, _count, _id, _production, _rhs, _seen, _backup
    _init           const __temporary, _temporary
    _init           const __bitset, _bitset
    _init           const __return, _return
    _init           const _follow, follow

    push            _destination, _result
    push            _self, _parser
    push            _select, _target
    push            _temporary,
    push            _id, 0H
    push            _count, 0H
    push            _change, 0H

    take            ,_control
    jno             _follow_init
    duptop          _control
    inc             _control
    jump            _follow_check
   _follow_init:
    push            _control, 0H
   _follow_check:
    match           =< _select =>, _select
    jno             _follow_pop
    _transformable  _self.=nonterminal?._select.=exist?
    jno             _follow_pop
    evaluate        _id, _self.=nonterminal?._select
    call            _unique, __temporary, _follow
    call            _bitset?._declare?, _destination
    cmpz            _control
    jno             _follow_append
    call            _unique, __bitset, _follow
    call            _bitset?._declare?, _bitset
   _follow_append:
    arrange         _select, {_id}
    call            _bitset?._member?, __return, _bitset, _select
    cmpz            _return
    jno             _follow_pop
    call            _bitset?._insert?, _bitset, _select
    expand          _holder, _self.=record?
   _follow_loop:
    setz            _change
    _iterate        _symbol*, _holder
      evaluate      _count, _self.=nonterminal?._symbol.=productions?
      _repeat       _count, _index:_constant?._zero?
        expand      _production, _self.=nonterminal?._symbol._index?
        setz        _seen
        _iterate    _rhs*, _production
          cmpz      _seen
          jno       _follow_include
          match     =<_select=>, _rhs
          _jnonext
          evaluate  _select, _self.=nonterminal?._select
          cmp       _select, _id
          _jnonext
          inc       _seen
          _continue
         _follow_include:
          setz      _seen
          match     =(_select=), _rhs
          jno       _follow_first
          arrange   _select, {_select}
          _incmbr   _return, __return, _destination, _select, _jnonext, inc _change
          _continue
         _follow_first:
          call      _first, _temporary, _self, _rhs
          _incsub   _return, __return, _destination, _temporary, _jnonext, inc _change
        _end        _iterate
        ;cmpz        _seen
        ;_jyesnext
        ;arrange     _select, <_symbol>
        ;call        _follow, _temporary, _self, _select
        ;_incsub     _return, __return, _destination, _temporary, _jnonext, inc _change
      _end          _repeat
    _end            _iterate
    ;cmpz            _change
    ;jno             _follow_loop
   _follow_pop:
    compute         _backup, _control
    pop             _destination, _self, _select, _control, _temporary, _change, _count, _id
    cmpz            _backup
    jno             _follow_finish
    call            _bitset?._destroy?, _bitset
   _follow_finish:
  end calminstruction

  calminstruction _first_symbol?: _result?*, _parser?*, _nullable?*, _symbol?*&
    local       _index, _many, _production, _item, _holder
    _init       var const _true, (not 0H)
    _init       var const _false, 0H
    match       =< _symbol =>, _symbol
    jno         _first_symbol_finish     
    call        _bitset?._declare?, _result
    publish     _nullable, _false
    arrange     _many, _parser.=nonterminal?._symbol.=productions?
    varrfsh     _many
    setz        _index
   _first_symbol_loop:
    check       (_index < _many)
    jno         _first_symbol_finish
    expand      _production, _parser.=nonterminal?._symbol._index?
    match       ,_production
    jno         _first_symbol_iterate
    publish     _nullable, _true
    jump        _first_symbol_update
   _first_symbol_iterate:
    _iterate    _item, _production
      match     =< _item =>, _item
      jyes      _first_symbol_nonterminal
      compute   _holder, _item
      arrange   _holder, {_holder}
      call      _bitset?._insert?, _result, _holder
      _break
     _first_symbol_nonterminal:
    _end        _iterate
   _first_symbol_update:
    inc         _index
    jump        _first_symbol_loop
   _first_symbol_finish:
  end calminstruction

  calminstruction _greibach_normal_form? _result?*
  end calminstruction

  _replacement? := 0H
  namespace _replacement?
    ?_terminal?     := 0H
    ?_nonterminal?  := 0H
  end namespace

  calminstruction _chomsky_normal_form? _result?*
    local           _holder, _return, _symbol, _count, _production, _check, _rhs, _replace,\
                        _remove, _insert, _reinstate, _lhs, _mark, _newform, _change, _first_1, _first_2
    _init           const __return, _return
    _init           const __replacement, _replacement
    _init           const _chomsky, chomsky
    _init           var const _zero, 0H
    call            _remove_epsilon?, _result
    call            _remove_unit_rules?, _result
    call            _remove_non_productive?, _result
    call            _remove_non_reachable?, _result
    expand          _holder, _result.=record?
    _iterate        _symbol*, _holder
      arrange       _lhs, <_symbol>
      arrange       _reinstate, _lhs ->
      arrange       _remove,
      expand        _count, _result.=nonterminal?._symbol.=productions?
      _repeat       _count, _index:0H
        evaluate    _check, _result.=nonterminal?._symbol._index?.=count?
        check       (_check <= 1H)
        _jyesnext
        expand      _production, _result.=nonterminal?._symbol._index?
        arrange     _newform,
        setz        _replace
        _iterate    _rhs*, _production
          match     =( _rhs =), _rhs
          jno       _chomsky_normal_form_append
          cmpz      _replace
          jno       _chomsky_normal_form_update
          arrange   _remove, _remove,_index
         _chomsky_normal_form_update:
          inc       _replace
          compute   _mark, _rhs
          expand    _return, __replacement?.=terminal?._mark?
          jyes      _chomsky_normal_form_include
          call      _unique?, __return, _chomsky
          restore   __replacement?.=terminal?._mark?
          assign    __replacement?.=terminal?._mark?, _return
         _chomsky_normal_form_include:
          arrange   _insert, <_return>
          call      _nonterminal?, _result, _zero, _insert
          arrange   _return, _insert -> (_rhs)
          call      _productions, _result, _return
          arrange   _rhs, _insert
         _chomsky_normal_form_append:
          arrange   _newform, _newform,_rhs
        _end        _iterate
        cmpz        _replace
        _jyesnext
        _delcma     _newform
        arrange     _reinstate, _reinstate _newform |
      _end          _repeat
      match         ,_remove
      _jyesnext
      _delcma       _remove
      call          _rules_out?, _result, _remove, _lhs
      match         _reinstate =|, _reinstate
      call          _productions, _result, _reinstate
    _end            _iterate
   _chomsky_normal_form_loop:
    setz            _change
    _iterate        _symbol*, _holder
      arrange       _lhs, <_symbol>
      empty         _remove
      arrange       _newform, _lhs ->
      evaluate      _count, _result.=nonterminal?._symbol.=productions?
      _repeat       _count, _index:0H
        evaluate    _check, _result.=nonterminal?._symbol._index?.=count?
        check       (_check >= 3H)
        _jnonext
        arrange     _remove, _remove, _index
        inc         _change
        expand      _production, _result.=nonterminal?._symbol._index?
        match       =< _first_1 => =, =< _first_2 => _production, _production
        arrange     _insert, <_first_1>,<_first_2>
        evaluate    _first_1, _result.=nonterminal?._first_1.=hash?
        evaluate    _first_2, _result.=nonterminal?._first_2.=hash?
        str         _first_1
        concatenate _first_1, _first_2
        compute     _mark, (+_first_1)
        expand      _return, __replacement?.=nonterminal?._mark?
        jyes        _chomsky_normal_form_merge
        call        _unique, __return, _chomsky
        restore     __replacement?.=nonterminal?._mark?
        assign      __replacement?.=nonterminal?._mark?, _return
       _chomsky_normal_form_merge:
        arrange     _return, <_return>
        call        _nonterminal?, _result, _zero, _return
        arrange     _newform, _newform _return _production |
        arrange     _insert, _return -> _insert
        call        _productions, _result, _insert
        _break   
      _end          _repeat
      match         ,_remove
      _jyesnext
      _delcma       _remove
      call          _rules_out?, _result, _remove, _lhs
      match         _newform =|, _newform
      call          _productions, _result, _newform
    _end            _iterate
    cmpz            _change
    jno             _chomsky_normal_form_loop
  end calminstruction

  calminstruction _mark_nullable? _result?*
    local           _holder, _symbol, _change, _count, _index, _check, _production, _item
    expand          _holder, _result.=record?
    _iterate        _symbol*, _holder
      assign        _result.=nonterminal?._symbol.=nullable?, _constant?._false?
      assign        _result.=nonterminal?._symbol.=discard?, _constant?._false?
    _end            _iterate
   _mark_nullable_loop:
    compute         _change, _constant?._false?
    _iterate        _symbol*, _holder
      evaluate      _check, _result.=nonterminal?._symbol.=nullable?
      cmpz          _check
      _jnonext
      evaluate      _count, _result.=nonterminal?._symbol.=productions?
      _repeat       _count, _index:_constant?._zero?
        expand      _production, _result.=nonterminal?._symbol._index?.=empty?
        match       ,_production
        jyes        _mark_nullable_discard
        _iterate    _item*, _production
          match     =<_item=>, _item
          jno       _mark_nullable_continue
          evaluate  _item, _result.=nonterminal?._item.=nullable?
          cmpz      _item
          jyes      _mark_nullable_continue
        _end        _iterate
        jump        _mark_nullable_found
       _mark_nullable_continue:
        _continue
       _mark_nullable_discard:
        assign      _result.=nonterminal?._symbol.=discard?, _constant?._true?
       _mark_nullable_found:
        assign      _result.=nonterminal?._symbol.=nullable?, _constant?._true?
        compute     _change, _constant?._true?
        _break
      _end          _repeat
    _end            _iterate
    cmpz            _change
    jno             _mark_nullable_loop
  end calminstruction

  calminstruction _appear_grammar? _result?*, _retsym?*, _retidx?*, _parser?*, _target?*&
    local           _holder, _symbol, _count, _rhs, _current
    match           =<_target=>, _target
    jno             _appear_grammar_finish
    stringify       _target
    expand          _holder, _parser.=record?
    _iterate        _symbol*, _holder
      evaluate      _count, _parser.=nonterminal?._symbol.=productions?
      _repeat       _count, _index:_constant?._zero?
        expand      _rhs, _parser.=nonterminal?._symbol._index?
        _iterate    _current*, _rhs
          match     =<_current=>, _current
          _jnonext
          evaluate  _current, _parser.=nonterminal?._current.=hash?
          cmp       _current, _target
          _jnonext
          publish   _retsym, _symbol
          publish   _retidx, _index
          publish   _result, _constant?._true?
          jump      _appear_grammar_finish
        _end        _iterate
      _end          _repeat
    _end            _iterate
    publish         _result, _constant?._false?
   _appear_grammar_finish:
  end calminstruction

  calminstruction _rules_out? _result?*, _productions?*, _target?*&
    local           _much, _hash, _production, _max, _bitset, _return, _lookup, _destination
    match           =<_target=>, _target
    jno             _rules_out_finish
    _unique         _bitset, rules
    _call           _bitset?._declare?, ~ _bitset
   _rules_out_loop:
    compute         _max, (not 0H)
    _iterate        _production*, _productions
      check         (_max < _production)
      _jnonext
      arrange       _lookup, {_production}
      _call         _bitset?._member?, _return, ~ _bitset, ~ _lookup
      cmpz          _return
      _jnonext 
      compute       _max, _production
    _end            _iterate
    check           (_max < _constant?._zero?)
    jyes            _rules_out_clean
    arrange         _lookup, {_max}
    _call           _bitset?._insert?, ~ _bitset, ~ _lookup
    evaluate        _much, _result.=nonterminal?._target.=productions?
    check           (_max >= _much)
    jyes            _rules_out_loop
    compute         _much, (_much - (_max + 1H))
    _repeat         _much, _index_1:_max, _index_2:(_max + 1H)
      movsym        _result.=nonterminal?._target._index_1?, _result.=nonterminal?._target._index_2?
      movsym        _result.=nonterminal?._target._index_1?.=hash?, _result.=nonterminal?._target._index_2?.=hash?
      movvar        _result.=nonterminal?._target._index_1?.=count?, _result.=nonterminal?._target._index_2?.=count?
      move          _result.=nonterminal?._target._index_1?.=cnflnter?, _result.=nonterminal?._target._index_2?.=cnflnter?
      move          _result.=nonterminal?._target._index_1?.=cnfrnter?, _result.=nonterminal?._target._index_2?.=cnfrnter?
      move          _result.=nonterminal?._target._index_1?.=cnfterm?, _result.=nonterminal?._target._index_2?.=cnfterm?
      ;_call         _production_duplicate?
    _end            _repeat
    evaluate        _much, _result.=nonterminal?._target.=productions?
    dec             _much
    arrange         _destination, _result.=nonterminal?._target._much?
    restore         _destination
    _call           _production_destroy?, ~ _destination
    assign          _result.=nonterminal?._target.=productions?, _much
    jump            _rules_out_loop
   _rules_out_clean:
    _call           _bitset?._destroy?, ~ _bitset
   _rules_out_finish:
  end calminstruction

  calminstruction _evict? _result?*, _target?*&
    local           _holder, _return, _reference, _production, _count, _check, _remove, _defined, _symbol, _record, _lookup
    _init           const __return, _return
    _init           const __reference, _reference
    _init           const __production, _production
    _init           const _empty,
    arrange         _lookup, _target
    match           =< _target =>, _target
    jno             _evict_finish
    expand          _defined, _result.=nonterminal?._target.=exist?
    jno             _evict_finish
    arrange         _remove,
    evaluate        _count, _result.=nonterminal?._target.=productions?
    _repeat         _count, _index:0H
      arrange       _remove, _remove,_index
    _end            _repeat
    _delcma         _remove
    call            _rules_out, _result, _remove, _lookup
   _evict_loop:
    call            _appear_grammar, __return, __reference, __production, _result, _lookup
    cmpz            _return
    jyes            _evict_refine
    arrange         _reference, <_reference>
    call            _rules_out, _result, _production, _reference
    jump            _evict_loop
   _evict_refine:
    evaluate        _defined, _result.=nonterminal?._target.=hash?
    arrange         _record,
    expand          _holder, _result.=record?
    _iterate        _symbol*, _holder
      evaluate      _check, _result.=nonterminal?._symbol.=hash?
      cmp           _defined, _check
      _jyesnext
      arrange       _record, _record,_symbol
    _end            _iterate
    _delcma         _record
    assign          _result.=record?, _record
    expand          _symbol, _result.=start?
    evaluate        _check, _result.=nonterminal?._symbol.=hash?
    cmp             _check, _defined
    jno             _evict_restore
    assign          _result.=start?, _empty
   _evict_restore:
    restore         _result.=nonterminal?._target.=hash?
    restore         _result.=nonterminal?._target.=exist?
    restore         _result.=nonterminal?._target.=list?
    restore         _result.=nonterminal?._target.=optional?
    restore         _result.=nonterminal?._target.=cache?
    restore         _result.=nonterminal?._target.=nullable?
    restore         _result.=nonterminal?._target.=discard?
    restore         _result.=nonterminal?._target.=productions?
    restore         _result.=nonterminal?._target
   _evict_finish:
  end calminstruction

  calminstruction _remove_epsilon? _result?*
    local           _change, _holder, _symbol, _count, _return, _candidate,\
                        _target, _production, _lookup, _once, _newform_1, _newform_2, _epsilon
   _remove_epsilon_loop:
    expand          _holder, _result.=record?
    _iterate        _symbol*, _holder
      assign        _result.=nonterminal?._symbol.=replacement?, _constant?._empty?
    _end            _iterate
   _remove_epsilon_evict:
    expand          _holder, _result.=record?
    _call           _mark_nullable, ~ _result
    _iterate        _symbol*, _holder
      arrange       _candidate, _symbol
      evaluate      _return, _result.=nonterminal?._symbol.=discard?
      cmpz          _return
      _jyesnext
      arrange       _lookup, <_symbol>
      _call         _appear_grammar, _return, _target, _production, ~ _result, ~ _lookup
      cmpz          _return
      _jnoexit
    _end            _iterate
    cmpz            _return
    jyes            _remove_epsilon_handle
    expand          _lookup, _result.=nonterminal?._candidate.=replacement?
    match           ,_lookup
    jno             _remove_epsilon_prepare
    _call           _unique, * _return, remove
    arrange         _lookup, _return
    arrange         _return, <_return>
    _call           _nonterminal, ~ _result, ~ _constant?._zero?, ~ _return
    assign          _result.=nonterminal?._candidate.=replacement?, _lookup
   _remove_epsilon_prepare:
    stringify       _candidate
    empty           _newform_1
    empty           _newform_2
    setz            _once
    expand          _holder, _result.=nonterminal?._target._production?
    _iterate        _symbol, _holder
      arrange       _current, _symbol
      match         =<_current=>, _current
      jno           _remove_epsilon_append
      evaluate      _return, _result.=nonterminal?._current.=hash?
      cmp           _return, _candidate
      jno           _remove_epsilon_append
      cmpz          _once
      jno           _remove_epsilon_append
      not           _once
      arrange       _newform_1, _newform_1, <_lookup>
      _continue
     _remove_epsilon_append:
      arrange       _newform_1, _newform_1, _symbol
      arrange       _newform_2, _newform_2, _symbol
    _end            _iterate
    _delcma         _newform_1
    _delcma         _newform_2
    arrange         _target, <_target>
    _call           _rules_out, ~ _result, ~ _production, ~ _target
    arrange         _production, _target -> _newform_1 | _newform_2
    _call           _productions, ~ _result, ~ _production
    jump            _remove_epsilon_evict
   _remove_epsilon_handle:
    setz            _change
    expand          _holder, _result.=record?
    _iterate        _symbol, _holder
      expand        _target, _result.=nonterminal?._symbol.=replacement?
      match         ,_target
      _jyesnext
      not           _change
      arrange       _lookup, <_target>
      arrange       _target, _lookup ->
      compute       _epsilon, (not 0H)
      evaluate      _count, _result.=nonterminal?._symbol.=productions?
      _repeat       _count, _index:_constant?._zero?
        expand      _production, _result.=nonterminal?._symbol._index?
        match       ,_production
        jno         _remove_epsilon_reset
        _continue
       _remove_epsilon_reset:
        arrange     _target, _target _production |
        setz        _epsilon
      _end          _repeat
      match         _target =|, _target
      cmpz          _epsilon
      jyes          _remove_epsilon_alternative
     _remove_epsilon_useless:
      _call         _appear_grammar, * _return, * _target, * _production, ~ _result, ~ _lookup
      arrange       _target, <_target>
      cmpz          _return
      _jyesnext
      _call         _rules_out, ~ _result, ~ _production, ~ _target
      jump          _remove_epsilon_useless
     _remove_epsilon_alternative:
      _call         _productions, ~ _result, ~ _target
    _end            _iterate
    cmpz            _change
    jno             _remove_epsilon_loop
   _remove_epsilon_finish:
    ;call            _remove_non_reachable?, _result
  end calminstruction

  macro calminstruction?._chain_rules? _target?*
    local       _target
    match       =< _target => _target, _target
    _jyesnext
    match       =< _target =>, _target
    _jnonext
  end macro

  calminstruction _remove_unit_rules? _result?*
    local               _holder, _symbol, _count, _production, _candidate, _remove, _list, _check, _lookup, _insert, _change
    _init               var const _true, (not 0H)
    _init               var const _false, 0H
   _remove_unit_rules_loop:
    arrange             _candidate,
    expand              _holder, _result.=record?
    _iterate            _symbol, _holder
      assign            _result.=nonterminal?._symbol.=cache?, _false
      match             ,_candidate
      _jnonext
      evaluate          _count, _result.=nonterminal?._symbol.=productions?
      _repeat           _count, _index:0H
        expand          _production, _result.=nonterminal?._symbol._index?
        _chain_rules    _production
        assign          _result.=nonterminal?._symbol.=cache?, _true
        arrange         _candidate, _symbol
      _end              _repeat
    _end                _iterate
    match               ,_candidate
    jyes                _remove_unit_rules_finish
    arrange             _lookup, <_candidate>
   _remove_unit_rules_strip:
    arrange             _remove,
    evaluate            _count, _result.=nonterminal?._candidate.=productions?
    _repeat             _count, _index:0H
      expand            _production, _result.=nonterminal?._candidate._index?
      _chain_rules      _production
      arrange           _remove, _remove, _index
      evaluate          _check, _result.=nonterminal?._production.=cache?
      cmpz              _check
      _jnonext
      assign            _result.=nonterminal?._production.=cache?, _true
      push              _list, _production
    _end                _repeat
    match               =,_remove, _remove
    arrange             _insert, _lookup ->
    setz                _change
    _unroll             _list
      evaluate          _count, _result.=nonterminal?._list.=productions?
      _repeat           _count, _index:0H
        expand          _production, _result.=nonterminal?._list._index?
        arrange         _insert, _insert _production |
        compute         _change, (not 0H)
      _end              _repeat
    _end                _unroll
    call                _rules_out, _result, _remove, _lookup
    cmpz                _change
    jyes                _remove_unit_rules_loop
    match               _insert =|, _insert
    call                _productions, _result, _insert
    jump                _remove_unit_rules_strip
   _remove_unit_rules_finish:
  end calminstruction

  calminstruction _remove_non_productive? _result?*
    local           _change, _holder, _symbol, _check, _count, _production, _rhs, _return, _target, _production
    _init           const __return, _return
    _init           const __target, _target
    _init           const __production, _production
    _init           var const _true, (not 0H)
    _init           var const _false, 0H
    expand          _holder, _result.=record?
    _iterate        _symbol*, _holder
      assign        _result.=nonterminal?._symbol.=cache?, _false
    _end            _iterate
   _remove_non_productive_mark:
    setz            _change
    _iterate        _symbol*, _holder
      evaluate      _check, _result.=nonterminal?._symbol.=cache?
      cmpz          _check
      _jnonext
      evaluate      _count, _result.=nonterminal?._symbol.=productions?
      _repeat       _count, _index:0H
        expand      _production, _result.=nonterminal?._symbol._index?
        _iterate    _rhs*, _production
          match     =< _rhs =>, _rhs
          _jnonext
          evaluate  _check, _result.=nonterminal?._rhs.=cache?
          cmpz      _check
          jyes      _remove_non_productive_retry
        _end        _iterate
        assign      _result.=nonterminal?._symbol.=cache?, _true
        inc         _change
       _remove_non_productive_retry:
      _end          _repeat
    _end            _iterate
    cmpz            _change
    jno             _remove_non_productive_mark
    _iterate        _symbol*, _holder
      evaluate      _check, _result.=nonterminal?._symbol.=cache?
      cmpz          _check
      _jnonext
      arrange       _symbol, <_symbol>
      call          _evict, _result, _symbol
    _end            _iterate
  end calminstruction

  calminstruction _remove_non_reachable? _result?
    local           _holder, _symbol, _check, _change, _production, _rhs
    _init           var const _unvisited, (not 1H)
    _init           var const _visited, (not 0H)
    _init           var const _zero, 0H
    expand          _holder, _result.=record?
    _iterate        _symbol*, _holder
      assign        _result.=nonterminal?._symbol.=cache?, _zero
    _end            _iterate
    expand          _symbol, _result.=start?
    assign          _result.=nonterminal?._symbol.=cache?, _unvisited
   _remove_non_reachable_loop:
    setz            _change
    _iterate        _symbol*, _holder
      evaluate      _check, _result.=nonterminal?._symbol.=cache?
      cmp           _check, _unvisited
      _jnonext
      evaluate      _count, _result.=nonterminal?._symbol.=productions?
      _repeat       _count, _index:0H
        expand      _production, _result.=nonterminal?._symbol._index?
        _iterate    _rhs*, _production
          match     =< _rhs =>, _rhs
          _jnonext
          evaluate  _check, _result.=nonterminal?._rhs.=cache?
          cmp       _check, _zero
          _jnonext
          assign    _result.=nonterminal?._rhs.=cache?, _unvisited
        _end        _iterate
      _end          _repeat
      assign        _result.=nonterminal?._symbol.=cache?, _visited
      inc           _change
    _end            _iterate
    cmpz            _change
    jno             _remove_non_reachable_loop
    _iterate        _symbol*, _holder
      evaluate      _check, _result.=nonterminal?._symbol.=cache?
      cmp           _check, _zero
      _jnonext
      arrange       _symbol, <_symbol>
      call          _evict, _result, _symbol
    _end            _iterate
  end calminstruction

  calminstruction _remove_cycle? _result?*
  end calminstruction

  calminstruction _immediate_left_recursion? _result?*
    local           _holder, _insert, _symbol, _hash, _count, _index, _production, _recursive,\
                        _first, _target, _suffix, _prime, _temporary, _copy_1, _copy_2
    _init           const __temporary, _temporary
    _init           const __prime, _prime
    _init           const _immediate, immediate
    _init           var const _true, (not 0H)
    _init           var const _false, 0H
    call            _unique, __temporary, _immediate
    call            _declare, _temporary
    expand          _holder, _result.=start?
    assign          _temporary.=start?, _holder
    expand          _holder, _result.=record?
    _iterate        _symbol, _holder
      arrange       _insert, <_symbol>
      call          _nonterminal, _temporary, _false, _insert
      evaluate      _hash, _result.=nonterminal?._symbol.=hash?
      evaluate      _count, _result.=nonterminal?._symbol.=productions?
      _repeat       _count, _index:0H
        compute     _recursive, _false
        expand      _production, _result.=nonterminal?._symbol._index?
        match       =< _first => _production?, _production
        jno         _immediate_left_recursion_push
        evaluate    _target, _result.=nonterminal?._first.=hash?
        check       (_hash = _target)
        jno         _immediate_left_recursion_patch
        match       =,_production, _production
        compute     _recursive, _true
        jump        _immediate_left_recursion_push
       _immediate_left_recursion_patch:
        arrange     _production, <_first> _production
       _immediate_left_recursion_push:
        assign      _result.=nonterminal?._symbol._index?.=cache?, _recursive
        cmpz        _recursive
        _jyesnext
        push        _suffix, _production
      _end          _repeat
      take          _suffix, _suffix
      jno           _immediate_left_recursion_default
      call          _unique, __prime, _immediate
      arrange       _prime, <_prime>
      call          _nonterminal, _temporary, _false, _prime
      arrange       _production, <_symbol> ->
      _repeat       _count, _index:0H
        evaluate    _recursive, _result.=nonterminal?._symbol._index?.=cache?
        cmpz        _recursive
        _jnonext
        expand      _target, _result.=nonterminal?._symbol._index?
        arrange     _production, _production _target, _prime |
      _end          _repeat
      match         _production =|, _production
      call          _productions, _temporary, _production
      arrange       _production, _prime ->
     _immediate_left_recursion_unroll:
      arrange       _production, _production _suffix, _prime |
      pop           _suffix
      take          _suffix, _suffix
      jyes          _immediate_left_recursion_unroll
      call          _productions, _temporary, _production
      _continue
   _immediate_left_recursion_default:
      arrange       _copy_1, _temporary.=nonterminal?._symbol
      arrange       _copy_2, _result.=nonterminal?._symbol
      call          _dupnter, _copy_1, _copy_2
    _end            _iterate
    call            _duplicate, _result, _temporary
  end calminstruction

  calminstruction _left_recursion_elimination? _result?*
    local       _temporary, _prime, _holder, _item_1, _item_2, _index_1, _index_2, _hash, _condition, _count_1, _count_2, _production, _first, _copy_1, _copy_2
    _init       const __temporary, _temporary
    _init       const __prime, _prime
    _init       const __first, _first
    _init       const _recursion, recursion
    _init       var const _zero, 0H
    call        _remove_cycle, _result

_init const __abc, _abc

    call        _unique, __temporary, _recursion
    call        _declare, _temporary
    expand      _holder, _result.=record?
    assign      _temporary.=record?, _holder
    setz        _index_1
    _iterate    _item_1, _holder
      inc       _index_1
      arrange   _copy_1, _temporary.=nonterminal?._item_1
      arrange   _copy_2, _result.=nonterminal?._item_1
      call      _dupnter, _copy_1, _copy_2
      setz      _index_2
      _iterate      _item_2, _holder
        inc         _index_2
        check       (_index_2 < _index_1)
        _jnoexit
        evaluate    _hash, _result.=nonterminal?._item_2.=hash?
        evaluate    _count_1, _result.=nonterminal?._item_1.=productions?
        _repeat     _count_1, _current:0H
          expand    _production, _result.=nonterminal?._item_1._current?
          assign    _temporary.=nonterminal?._item_1._current?, _production

arrange _abc, _production
stringify _abc

          match     =< _first => _production?, _production
          _jnonext
          expand    _condition, _result.=nonterminal?._first.=hash?
          jno       _left_recursion_elimination_warning
          check     (_hash = _condition)
          _jnonext

          ;_asmcmd   =display "FOUND: ", __abc, 00AH

          ;call      _unique, __prime, _recursion
          ;arrange   _prime, <_prime>
          ;call      _nonterminal, _temporary, _zero, _prime
          ;arrange   _production, _prime _production
          ;assign    _temporary.=nonterminal?._item_1._current?, _production

          evaluate  _decrement, _temporary.=nonterminal?._item_1.=productions?
          dec       _decrement
          assign    _temporary.=nonterminal?._item_1.=productions?, _decrement
          arrange   _suffix, _production
          evaluate  _count_2, _result.=nonterminal?._first.=productions?
          _repeat   _count_2, _target:0H
            expand  _production, _result.=nonterminal?._first._target?
            arrange _production, <_item_1> -> _production _suffix
            call    _productions, _temporary, _production
          _end      _repeat
          _continue
         _left_recursion_elimination_warning:
          stringify _first
          _asmcmd   =display "parser: warning non-terminal is not defined: ", __first, 00AH
        _end    _repeat
      _end      _iterate
      
      evaluate      _hash, _result.=nonterminal?._item_1.=hash?
      evaluate      _count_1, _result.=nonterminal?._item_1.=productions?
      _repeat       _count_1, _current:0H
        expand    _production, _result.=nonterminal?._item_1._current?
      _end          _repeat
    _end        _iterate
    ;call        _duplicate, _result, _temporary
    ;call        _display, _temporary
  end calminstruction

  calminstruction _alternative_prefix? _common?, _remain?, _length?, _parser?*, _symbol?*, _production_1?*, _production_2?*
    local           _first_1, _first_2, _hash_1, _hash_2, _size, _prefix
    varrfsh         _production_1
    expand          _production_1, _parser.=nonterminal?._symbol._production_1?
    varrfsh         _production_2
    expand          _production_2, _parser.=nonterminal?._symbol._production_2?
    arrange         _first_2,
    arrange         _prefix,
    setz            _size
   _alternative_prefix_loop:
    match           =< _first_1 => _production_1?, _production_1
    jyes            _alternative_prefix_nonterminal
    match           =( _first_1 =) _production_1?, _production_1
    jno             _alternative_prefix_adjust
    match           =( _first_2 =) _production_2?, _production_2
    jno             _alternative_prefix_adjust
    compute         _hash_1, _first_1
    compute         _hash_2, _first_2
    arrange         _first_2, (_first_2)
    jump            _alternative_prefix_equal
   _alternative_prefix_nonterminal:
    match           =< _first_2 => _production_2?, _production_2
    jno             _alternative_prefix_adjust
    evaluate        _hash_1, _parser.=nonterminal?._first_1.=hash?
    evaluate        _hash_2, _parser.=nonterminal?._first_2.=hash?
    arrange         _first_2, <_first_2>
   _alternative_prefix_equal:
    cmp             _hash_1, _hash_2
    jno             _alternative_prefix_patch
    arrange         _prefix, _prefix,_first_2
    match           =,_production_1, _production_1
    match           =,_production_2, _production_2
    inc             _size
    jump            _alternative_prefix_loop
   _alternative_prefix_patch:
    arrange         _production_2, _first_2 _production_2
   _alternative_prefix_adjust:
    match           =,_prefix, _prefix
    match           ,_common
    jyes            _alternative_prefix_remain
    publish         _common, _prefix
   _alternative_prefix_remain:
    match           ,_remain
    jyes            _alternative_prefix_length
    publish         _remain, _production_2
   _alternative_prefix_length:
    match           ,_length
    jyes            _alternative_prefix_finish
    publish         _length, _size
   _alternative_prefix_finish:
  end calminstruction

  calminstruction _left_factoring? _result?*
    local                   _temporary, _holder, _lookup, _return, _symbol, _global, _gather, _count, _index_1, _index_2,\
                                _prefix, _suffix, _selected, _min, _size, _item, _insert, _first, _target, _change
    _init                   const __temporary, _temporary
    _init                   const __return, _return
    _init                   const __global, _global
    _init                   const __gather, _gather
    _init                   const __prefix, _prefix
    _init                   const __suffix, _suffix
    _init                   const __size, _size
    _init                   const _factoring, factoring
    _init                   const _empty,
    _init                   var const _zero, 0H
    call                    _unique, __global, _factoring
    call                    _unique, __gather, _factoring
   _left_factoring_loop:
    setz                    _change
    call                    _unique, __temporary, _factoring
    call                    _declare, _temporary
    expand                  _holder, _result.=record?
    _iterate                _symbol, _holder
      call                  _bitset?._declare?, _global
      arrange               _lookup, <_symbol>
      call                  _nonterminal, _temporary, _zero, _lookup
      evaluate              _count, _result.=nonterminal?._symbol.=productions?
      _repeat               _count, _index_1:0H
        compute             _target, _index_1
        arrange             _lookup, {_index_1}
        call                _bitset?._member?, __return, _global, _lookup
        cmpz                _return
        _jnonext
        call                _bitset?._declare?, _gather
        setz                _min
        _repeat             ((_count - _index_1) - 1H), _index_2:(_index_1 + 1H)
          call              _alternative_prefix, __prefix, __suffix, __size, _result, _symbol, _index_1, _index_2
          cmpz              _size
          _jyesnext
          assign            _result.=nonterminal?._symbol._index_2?.=cache?, _suffix
          check             ((_size = _min) | (~ _min))
          jyes              _left_factoring_gather
          check             (_size > _min)
          _jyesnext
          _bitset_foreach   _gather, _target
            call            _alternative_prefix, _empty, __suffix, _empty, _result, _symbol, _index_2, _target
            assign          _result.=nonterminal?._symbol._target?.=cache?, _suffix
          _end              _foreach
         _left_factoring_gather:
          arrange           _lookup, {_index_2}
          call              _bitset?._insert?, _gather, _lookup
          arrange           _selected, _prefix
          compute           _target, _index_2
          compute           _min, _size
        _end                _repeat
        call                _alternative_prefix, __prefix, __suffix, _empty, _result, _symbol, _target, _index_1
        assign              _result.=nonterminal?._symbol._index_1?.=cache?, _suffix
        arrange             _insert, <_symbol> -> _prefix
        call                _bitset?._union?, _global, _gather
        call                _bitset?._empty?, __return, _gather
        cmpz                _return
        jno                 _left_factoring_insert
        not                 _change
        arrange             _lookup, {_index_1}
        call                _bitset?._insert?, _gather, _lookup
        call                _unique, __return, _factoring
        arrange             _lookup, <_return>
        call                _nonterminal, _temporary, _zero, _lookup
        _bitset_foreach     _gather, _item, _first
          expand            _suffix, _result.=nonterminal?._symbol._item?.=cache?
          arrange           _insert, _insert | _suffix
          cmpz              _first
          _jyesnext
          arrange           _insert, _lookup -> _suffix
        _end                _foreach
        call                _productions, _temporary, _insert
        arrange             _insert, <_symbol> -> _selected, _lookup
       _left_factoring_insert:
        call                _productions, _temporary, _insert
      _end                  _repeat
    _end                    _iterate
    expand                  _holder, _result.=start?
    assign                  _temporary.=start?, _holder
    call                    _duplicate, _result, _temporary
    cmpz                    _change
    jno                     _left_factoring_loop
  end calminstruction

  calminstruction _cyk_parsing? _result?*, _recognition?*, _grammar?*, _debug?*, _sentences?*&
    local               _length, _holder, _symbol, _count, _check, _token, _slice, _split, _position, _print, _trash, _first, _second, _append, _left, _right, _lconcat, _rconcat, _front_1, _front_2, _merge, _final, _start, _bitset, _cache, _insert, _hash, _proxy
    _init               const __print, _print
    _init               const __bitset, _bitset
    _init               const __merge, _merge
    _init               const _CYK, CYK
    _init               const _empty,
    _init               var const _true, (not 0H)
    _init               var const _false, 0H
    _init               var const _zero, 0H
    assign              _recognition, _zero
    assign              _recognition.=substring?, _zero
    assign              _recognition.=rightside?, _zero
    assign              _recognition.=lookdefnd?, _zero
    ;call                _chomsky_normal_form, _grammar
    call                _unique, __bitset, _CYK
    call                _unique, __merge, _CYK
    varrfsh             _debug
    setz                _length
    _iterate            _token*, _sentences
      inc               _length 
    _end                _iterate
    expand              _holder, _grammar.=record?
    setz                _split
   _cyk_parsing_loop:
    setz                _position
    empty               _slice
    _iterate            _token*, _sentences
      arrange           _slice, _slice._token
      cmp               _position, _split
      jno               _cyk_parsing_update
      ;_delcma           _slice
      match             =._slice, _slice
      ;_cyk_lookup       _hash, _slice
      cmpz              _split
      jno               _cyk_parsing_foreach
      call              _bitset?._declare?, _bitset
      ;empty             _append
      _iterate          _symbol*, _holder
        evaluate        _count, _grammar.=nonterminal?._symbol.=productions?
        _repeat         _count, _index:0H
          ;evaluate      _check, _grammar.=nonterminal?._symbol._index?.=count?
          ;cmp           _check, 1H
          ;_jnonext
          ;expand        _check, _grammar.=nonterminal?._symbol._index?
          ;match         =( _check =), _check
          expand        _check, _grammar.=nonterminal?._symbol._index?.=cnfterm?
          _jyesnext
          cmp           _check, _slice
          _jnonext
          evaluate      _insert, _grammar.=nonterminal?._symbol
          arrange       _insert, {_insert}
          call          _bitset?._insert?, _bitset, _insert
          ;arrange       _append, _append,_symbol
          _break
        _end            _repeat
      _end              _iterate
      ;_delcma           _append
      ;match             ,_append
      ;jyes              _cyk_parsing_finish
      ;_cyk_lookup       _cache, _slice
      arrange           _cache, _recognition.=substring?._slice
      call              _bitset?._duplicate?, _cache, _bitset
      ;assign            __recognition?.=_substring?._lookup?, _append

      ;cmpz              _debug
      ;jyes              _cyk_parsing_sanitize
      ;arrange           _print, _slice
      ;stringify         _print
      ;_asmcmd           =display "SUBSTRING = [", __print, "] -> "
      ;arrange           _print, _append
      ;stringify         _print
      ;_asmcmd           =display __print, 00AH

      jump              _cyk_parsing_sanitize
     _cyk_parsing_foreach:
      call              _bitset?._declare?, _merge
      ;empty             _merge
      empty             _first
      arrange           _second, _slice
     _cyk_parsing_substring:
      match             _append=._second, _second
      jno               _cyk_parsing_strip
      arrange           _first, _first._append
      ;_delcma           _first
      match             =._first, _first
      ;_cyk_lookup       _left, _first
      ;_cyk_lookup       _right, _second

      ;arrange           _left, _first
      ;arrange           _right, _second
      ;symnum            _left
      ;symnum            _right
      ;expand            _left, __recognition?.=_substring?._left?
      ;expand            _right, __recognition?.=_substring?._right?
      arrange           _left, _recognition.=substring?._first
      arrange           _right, _recognition.=substring?._second
      ;_iterate          _lconcat*, _left
      _bitset_foreach   _left, _lconcat
        ;compute         _lhash, _lconcat
        ;evaluate        _lhash, _grammar.=nonterminal?._lconcat
        ;evaluate        _lhash, _grammar.=nonterminal?._lconcat.=hash?
        ;_iterate        _rconcat*, _right
        _bitset_foreach _right, _rconcat
          ;compute       _rhash, _rconcat
          ;evaluate      _rhash, _grammar.=nonterminal?._rconcat
          ;evaluate      _rhash, _grammar.=nonterminal?._rconcat.=hash?
          arrange       _proxy, _lconcat._rconcat
          ;_cyk_lookup   _lookup, _proxy
          ;arrange       _lookup, _lconcat,_rconcat
          ;symnum        _lookup
          arrange       _cache, _recognition.=rightside?._proxy
          expand        _append, _recognition.=lookdefnd?._proxy
          jyes          _cyk_parsing_concatenate
          ;empty         _append
          call          _bitset?._declare?, _bitset
          _iterate      _symbol*, _holder
            evaluate    _count, _grammar.=nonterminal?._symbol.=productions?
            _repeat     _count, _index:0H
              expand    _front_1, _grammar.=nonterminal?._symbol._index?.=cnflnter?
              _jyesnext
              varrfsh   _front_1
              evaluate  _front_2, _grammar.=nonterminal?._symbol._index?.=cnfrnter?
              ;evaluate  _check, _grammar.=nonterminal?._symbol._index?.=count?
              ;cmp       _check, 2H
              ;_jnonext
              ;expand    _check, _grammar.=nonterminal?._symbol._index?
              ;match     =< _front_1 => =, =< _front_2 =>, _check
              ;evaluate  _front_1, _grammar.=nonterminal?._front_1.=hash?
              ;evaluate  _front_2, _grammar.=nonterminal?._front_2.=hash?
              check     ((_lconcat = _front_1) & (_rconcat = _front_2))
              _jnonext
              ;arrange   _append, _append,_symbol
              evaluate  _insert, _grammar.=nonterminal?._symbol
              arrange   _insert, {_insert}
              call      _bitset?._insert?, _bitset, _insert
              _break
            _end        _repeat
          _end          _iterate
          ;_delcma       _append
          ;match         ,_append
          ;_jyesnext
          restore       _recognition.=lookdefnd?._proxy
          assign        _recognition.=lookdefnd?._proxy, _empty
          call          _bitset?._duplicate?, _cache, _bitset
          ;assign        __recognition?.=_rightside?._lookup?, _append
         _cyk_parsing_concatenate:
          ;arrange       _merge, _append
          call          _bitset?._union?, _merge, _cache
        ;_end            _iterate
        _end            _foreach
      ;_end              _iterate
      _end              _foreach

      ;cmpz              _debug
      ;jyes              _cyk_parsing_substring
      ;arrange           _print, _first
      ;stringify         _print
      ;_asmcmd           =display "(FIRST:", __print, ",SECOND:"
      ;arrange           _print, _second
      ;stringify         _print
      ;_asmcmd           =display __print, ") "

      jump              _cyk_parsing_substring
     _cyk_parsing_strip:
      ;_iterate          _symbol*, _holder
      ;  assign          _grammar.=nonterminal?._symbol.=cache?, _false
      ;_end              _iterate
      ;empty             _final
      ;_iterate          _symbol*, _merge
      ;  evaluate        _check, _grammar.=nonterminal?._symbol.=cache?
      ;  assign          _grammar.=nonterminal?._symbol.=cache?, _true
      ;  cmpz            _check
      ;  _jnonext
      ;  arrange         _final, _final,_symbol
      ;_end              _iterate
      ;_delcma           _final

      ;arrange           _lookup, _slice
      ;symnum            _lookup
      ;_cyk_lookup       _lookup, _slice
      ;assign            __recognition?.=_substring?._lookup?, _final

      ;_cyk_lookup       _cache, _slice
      arrange           _cache, _recognition.=substring?._slice
      call              _bitset?._duplicate?, _cache, _merge
    
      ;cmpz              _debug
      ;jyes              _cyk_parsing_sanitize
      ;arrange           _print, _slice
      ;stringify         _print
      ;_asmcmd           =display "SUBSTRING = [", __print, "]", 00AH
      ;arrange           _print, _final
      ;stringify         _print
      ;_asmcmd           =display __print, 00AH

     _cyk_parsing_sanitize:
      match             _trash _slice?, _slice
      _continue
     _cyk_parsing_update:
      inc               _position
    _end                _iterate
    ;_asmcmd             =display 00AH
    inc                 _split
    check               (_split < _length)
    jyes                _cyk_parsing_loop

    call                _bitset?._display?, _cache
    exit

    expand              _start, _grammar.=start?
    evaluate            _start, _grammar.=nonterminal?._start.=hash?
    ;expand              _holder, __recognition?.=_substring?._lookup?
    _iterate            _symbol*, _holder
      evaluate          _check, _grammar.=nonterminal?._symbol.=hash?
      cmp               _check, _start
      _jnonext
      assign            _result, _true
      exit
    _end                _iterate
   _cyk_parsing_finish:
    assign              _result, _false
  end calminstruction

  calminstruction _cyk_derivation? _result?*, _table?*, _grammar?*, _sentences?*&
    local           _lookup, _start, _return, _translate, _item
    _init           const __return, _return
    _init           var const _zero, 0H
    expand          _start, _grammar.=start?
    evaluate        _start, _grammar.=nonterminal?._start
    arrange         _start, {_start}
    empty           _translate
    _iterate        _item*, _sentences
      arrange       _translate, _translate=._item
    _end            _iterate
    match           =._translate, _translate
    arrange         _lookup, _table.=substring?._translate
    call            _bitset?._member?, __return, _lookup, _start
    assign          _result, _return
  end calminstruction

  calminstruction _display? _result?*
    local           _holder, _item, _many, _index, _symbol, _lhs, _rhs, _nullable
    _init           const __holder, _holder
    _init           const __symbol, _symbol
    _init           const __lhs, _lhs
    _asmcmd         =display "START = "
    expand          _holder, _result.=start?
    stringify       _holder
    _asmcmd         =display __holder, 00AH
    expand          _holder, _result.=record?
    _iterate        _item*, _holder
      arrange       _lhs, _item
      stringify     _lhs
      arrange       _many, _result.=nonterminal?._item.=productions?
      varrfsh       _many
      setz          _index
     _display_loop:
      check         (_index < _many)
      _jnonext
      _asmcmd       =display "<", __lhs, "> -> "
      expand        _rhs, _result.=nonterminal?._item._index?
      _iterate      _symbol, _rhs
        match       =( _symbol =), _symbol
        stringify   _symbol
        _asmcmd     =display __symbol, 020H
      _end          _iterate
      _asmcmd       =display 00AH
      inc           _index
      jump          _display_loop  
    _end            _iterate
    _asmcmd         =display "NULLABLE = "
    call            _mark_nullable, _result
    _iterate        _symbol*, _holder
      evaluate      _nullable, _result.=nonterminal?._symbol.=nullable?
      cmpz          _nullable
      _jyesnext
      _asmcmd       =display =string(_result.=nonterminal?._symbol.=hash?), ","
    _end            _iterate
    _asmcmd         =display 00AH
  end calminstruction
end namespace
