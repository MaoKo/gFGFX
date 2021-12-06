
; <regex>           ->  <regex_union>                       {}
; <regex_union>     ->  <regex_cat> <regex_union'>          {}
; <regex_union'>    ->  '|' <regex_union>                   {}
;                   |                                       {}
; <regex_cat>       ->  <regex_closure> <regex_cat'>        {}
; <regex_cat'>      ->  <regex_cat>                         {}
;                   |                                       {}
; <regex_closure>   ->  <regex_atom> { _regex_closure'._result := _regex_atom._result }
;   <regex_closure'> { _regex_closure._result := ??? }
; <regex_closure'>  ->  '*' <regex_closure'>                {}
;                   |   '+' <regex_closure'>                {}
;                   |   '?' <regex_closure'>                {}
;                   |                                       {}
; <regex_atom>      ->  <regex_char>                        { _regex_atom._result := _regex_char._result }
;                   |   '(' <regex_union> ')'               {}
;                   |   '.'                                 {}
; <regex_char>      ->  REGCHAR                             { _regex_char._result := _automata_create({0},REGCHAR,{1}); }

;struc _regex_meta _tokenname?*, _skippable?*
;   .tokenname?:  db _tokenname
;   .skippable?:  db _skippable
;end struc

;struc _regex? _automata_start?*, _automata_stcnt?*,\
;           _automata_states_elems?*, _automata_states_count?*,\
;           _automata_accept_elems?*, _automata_accept_count?*,\
;           _automata_transition_elems?*, _automata_transition_count?*
;   .machine? _automata? _automata_start, _automata_stcnt, _automata_states_elems, _automata_states_count,\
;       _automata_accept_elems, _automata_accept_count, _automata_transition_elems, _automata_transition_count
;   .tokenname?: db _tokenname
;end struc

_regex? := 0H
namespace _regex?
  calminstruction _regex_meta? _result?*, _tokenname?*, _skippable?*
    varrfsh     _skippable
    assign      _result.=tokenname?, _tokenname
    assign      _result.=skippable?, _skippable
  end calminstruction

  calminstruction _regex_meta_duplicate? _result?*, _target?*
    movstr      _result.=tokenname?, _target.=tokenname?
    movvar      _result.=skippable?, _target.=skippable?
  end calminstruction

  macro calminstruction?._meta? _result?*
    assign      _result.=meta?, _constant?._zero?
  end macro

  calminstruction _declare? _result?*, _skippable?*, _alias?
    local       _holder, _name
    arrange     _holder, _result.=machine?
    _call       _automata?._declare?, ~ _holder
    _meta       _result
    match       ,_alias
    jno         _declare_finish
    arrange     _name, _result
    stringify   _name
    arrange     _holder, _result.=meta?
    _call       _regex_meta?, ~ _holder, ~ _name, ~ _skippable
   _declare_finish:
  end calminstruction

  calminstruction _duplicate? _result?*, _regex?*
    local       _holder_1, _holder_2
    arrange     _holder_1, _result.=machine?
    arrange     _holder_2, _regex.=machine?
    _call       _automata?._duplicate?, ~ _holder_1, ~ _holder_2
    _meta       _result
    arrange     _holder_1, _result.=meta?
    arrange     _holder_2, _regex.=meta?
    _call       _regex_meta_duplicate, ~ _holder_1, ~ _holder_2
  end calminstruction

  calminstruction _destroy? _result?*
    _asmcmd =TODO
  end calminstruction

  calminstruction _match? _result?*, _regex?*, _string?*
    arrange     _regex, _regex.=machine?
    _call       _automata?._accept?, ~ _resut, ~ _string, ~ _regex
  end calminstruction

  calminstruction _advance_stream? _result?*, _token?*, _errmsg?
    local       _input
    _cstwrp     _errmsg
    compute     _input, _result
   _advance_stream_loop:
    cmp         string(_token), _constant?._nullstr?
    jyes        _advance_stream_publish
    cmp         (_input and _constant?._byte_mask?), (_token and _constant?._byte_mask?)
    jyes        _advance_stream_shift
    match       ,_errmsg
    jno         _advance_stream_error
    compute     _errmsg, "regex: token unexpected"
   _advance_stream_error:
    _asmcmd     =err __errmsg
    compute     _input, _constant?._nullstr?
    jump        _advance_stream_publish
   _advance_stream_shift:
    shr         _token, 8H
    shr         _input, 8H
    jump        _advance_stream_loop
   _advance_stream_publish:
    str         _input
    publish     _result, _input
  end calminstruction

  _bound? := 0H
  namespace _bound?
  end namespace
  _cstwrp _bound

  _init sym const _brace_alias?, ALIAS
  _init sym const _brace_sequence?, SEQUENCE

  match _1 _2, _brace_alias _brace_sequence
    calminstruction _regex_brace? _result?*, _stream?*, _kind?*
      local       _return, _alias, _input, _current, _min, _max
      _call       _advance_stream, ~ _stream, ~ _constant?._lbrace?, ~ _constant?._empty?
      match       =_1?, _kind
      jyes        _regex_brace_alias
      match       =_2?, _kind
      jyes        _regex_brace_sequence
      _asmcmd     =err "Bad directive"
      exit
     _regex_brace_alias: 
      setz        _alias
      str         _alias
      compute     _input, _stream
     _regex_brace_loop:
      cmp         string(_input), _constant?._nullstr?
      jyes        _regex_brace_publish
      compute     _current, (_input and _constant?._byte_mask?)
      cmp         _current, _constant?._rbrace?
      jyes        _regex_brace_lookup
      concatenate _alias, _current
      shr         _input, 8H
      jump        _regex_brace_loop
     _regex_brace_lookup:
      varrfsh     _alias
      arrange     _alias, __bound?.=_#_alias?.=machine?
      _call       _automata?._empty?, _return, ~ _result
      cmpz        _return
      jyes        _regex_brace_concat
      _call       _automata?._duplicate?, ~ _result, ~ _alias
      jump        _regex_brace_publish
     _regex_brace_concat:
      _call       _automata?._thompson_concat?, ~ _result, ~ _alias
     _regex_brace_publish:
      str         _input
      publish     _stream, _input
      jump        _regex_brace_finish
     _regex_brace_sequence:
      _call       _unsigned_atoi, _min, ~ _stream, ~ _constant?._base_decimal?, ~ _constant?._empty?
      check       (_min < 0H)
      jno         _regex_brace_sequence_follow
      _asmcmd     =err "regex: missing digit after the '{'"
      jump        _regex_brace_finish
     _regex_brace_sequence_follow:
      cmp         (_stream and _constant?._byte_mask?), _constant?._comma?
      jno         _regex_brace_sequence_finite
      _call       _advance_stream, ~ _stream, ~ _constant?._comma?
      cmp         (_stream and _constant?._byte_mask?), _constant?._rbrace?
      jyes        _regex_brace_sequence_infinite
      _call       _unsigned_atoi, _max, ~ _stream
      check       (_max < 0H)
      jno         _regex_brace_sequence_range
      _asmcmd     =err "regex: missing digit after the ',' in the sequence"
      jump        _regex_brace_finish
     _regex_brace_sequence_range:
      symrfsh     _max
      _call       _automata?._finite_sequence?, ~ _result, ~ _min, ~ _max
      jump        _regex_brace_finish
     _regex_brace_sequence_infinite:
      _call       _automata?._infinite_sequence?, ~ _result, ~ _min
      jump        _regex_brace_finish
     _regex_brace_sequence_finite:
      _call       _automata?._finite_sequence?, ~ _result, ~ _min, ~ _constant?._empty?
     _regex_brace_finish:
      _call       _advance_stream, ~ _stream, ~ _constant?._rbrace?
    end calminstruction
  end match

  calminstruction _regex_char? _result?*, _stream?*
    local       _current, _escape
    _init       sym const _octal_size, 3H
    _init       sym const _hexadecimal_size, 2H
    _asmcmd     =assert (_stream <> =_constant?.=_nullstr?)
    compute     _current, (_stream and _constant?._byte_mask?)
    _call       _advance_stream, ~ _stream, ~ _current, ~ _constant?._empty?
    cmp         _current, '\'
    jno         _regex_char_publish
    check       (~lengthof(_stream))
    jno         _regex_char_continue
    _asmcmd     =err "regex: '\' can't terminate a regex without any character following it"
    jump        _regex_char_finish
   _regex_char_continue:
    compute     _escape, (_stream and _constant?._byte_mask?)
    cmp         _escape, 'n'
    compute     _current, 00AH
    jyes        _regex_char_adjust
    cmp         _escape, 'a'
    compute     _current, 7H
    jyes        _regex_char_adjust
    cmp         _escape, 'b'
    compute     _current, 8H
    jyes        _regex_char_adjust
    cmp         _escape, 'f'
    compute     _current, 00CH
    jyes        _regex_char_adjust
    cmp         _escape, 'r'
    compute     _current, 00DH
    jyes        _regex_char_adjust
    cmp         _escape, 't'
    compute     _current, 9H
    jyes        _regex_char_adjust
    cmp         _escape, 'v'
    compute     _current, 00BH
    jyes        _regex_char_adjust
    setz        _current
    cmp         (_escape or 020H), 'x'
    jno         _regex_char_octal
    _call       _advance_stream, ~ _stream, ~ _escape, ~ _constant?._empty?
    _call       _unsigned_atoi, _current, ~ _stream, ~ _constant?._base_hexadecimal?, ~ _hexadecimal_size
    check       (_current >= 0H)
    jyes        _regex_char_publish
    _asmcmd     =err "regex: hexadecimal constant must follow '\x' or '\X'"
    jump        _regex_char_finish
   _regex_char_octal:
    _call       _unsigned_atoi, * _current, ~ _stream, ~ _constant?._base_octal?, ~ _octal_size
    check       ((_current >= 0H) & (_current <= _constant?._byte_mask?))
    jyes        _regex_char_publish
    check       (_current > _constant?._byte_mask?)
    compute     _current, _escape
    jno         _regex_char_adjust
    _asmcmd     =err "regex: octal sequence out of range"
    jump        _regex_char_finish
   _regex_char_adjust:
    _call       _advance_stream,  ~ _stream, ~ _escape, ~ _constant?._empty?
   _regex_char_publish:
    publish     _result, _current
   _regex_char_finish:
  end calminstruction

  _init sym const _state_1?, {0H}
  _init sym const _state_2?, {1H}

  calminstruction _regex_apply_isensitive? _result?*, _insensitive?*, _symbol?*
    _call       _automata?._transition?, ~ _result, ~ _regex?._state_1?, ~ _symbol, ~ _regex?._state_2?
    cmpz        _insensitive
    jyes        _regex_apply_isensitive_finish
    _is_alpha   _symbol
    jno         _regex_apply_isensitive_finish
    xor         _symbol, 020H
    _call       _automata?._transition?, ~ _result, ~ _regex?._state_1?, ~ _symbol, ~ _regex?._state_2?
   _regex_apply_isensitive_finish:
  end calminstruction

  calminstruction _regex_symbol? _result?*, _insensitive?*, _stream?*
    local       _symbol
    _call       _regex_char, _symbol, ~ _stream
    _call       _regex_apply_isensitive, ~ _result, ~ _insensitive, ~ _symbol
  end calminstruction

  macro _cce_range? _target?*, _min?*, _max?*
    local _
    repeat (((_max) - (_min)) + 1H) _:(_min)
      _bitset?._insert? _target, {_}
    end repeat
  end macro
 
  _bitset?._declare? _cce_upper?
  _cce_range? _cce_upper?, 'A', 'Z'

  _bitset?._declare? _cce_lower?
  _cce_range? _cce_lower?, 'a', 'z'

  _bitset?._declare? _cce_digit?
  _cce_range? _cce_digit?, '0', '9'

  _bitset?._declare? _cce_space?
  _cce_range? _cce_space?, 9H, 00DH
  _bitset?._insert? _cce_space?, {' '}

  _bitset?._declare? _cce_blank?
  _bitset?._insert? _cce_blank?, {9H}
  _bitset?._insert? _cce_blank?, {' '}

  _bitset?._declare? _cce_cntrl?
  _cce_range? _cce_cntrl?, 0H, 01FH
  _bitset?._insert? _cce_cntrl?, {07FH}

  _bitset?._duplicate? _cce_alpha?, _cce_lower?
  _bitset?._union? _cce_alpha?, _cce_upper?

  _bitset?._duplicate? _cce_alnum?, _cce_alpha?
  _bitset?._union? _cce_alnum?, _cce_digit?
 
  _bitset?._duplicate? _cce_print?, _cce_cntrl?
  _bitset?._negate_byte? _cce_print?

  _bitset?._duplicate? _cce_graph?, _cce_print?
  _bitset?._delete? _cce_graph?, {' '}

  _bitset?._duplicate? _cce_punct?, _cce_graph?
  _bitset?._union? _cce_punct?, _cce_alnum?

  _bitset?._duplicate? _cce_xdigit?, _cce_digit?
  _cce_range? _cce_xdigit?, 'A', 'F'
  _cce_range? _cce_xdigit?, 'a', 'f'

  iterate _kind?*, alnum,alpha,cntrl,digit,graph,lower,print,punct,space,blank,upper,xdigit
    _bitset?._duplicate? _cce_#n#_kind?, _cce_#_kind?
    _bitset?._negate_byte? _cce_#n#_kind?
  end iterate
 
  calminstruction _regex_lone_ccl? _result?*, _insensitive?*, _stream?*
    local           _negate, _bound_1, _bound_2, _slice, _posix, _item, _lookup
    _init           const     __cce_alnum, _regex?._cce_alnum?
    _init           const     __cce_alpha, _regex?._cce_alpha?
    _init           const     __cce_cntrl, _regex?._cce_cntrl?
    _init           const     __cce_digit, _regex?._cce_digit?
    _init           const     __cce_graph, _regex?._cce_graph?
    _init           const     __cce_lower, _regex?._cce_lower?
    _init           const     __cce_print, _regex?._cce_print?
    _init           const     __cce_punct, _regex?._cce_punct?
    _init           const     __cce_space, _regex?._cce_space?
    _init           const     __cce_blank, _regex?._cce_blank?
    _init           const     __cce_upper, _regex?._cce_upper?
    _init           const   __cce_xdigit, _regex?._cce_xdigit?
    _init           const   __cce_nalnum, _regex?._cce_nalnum?
    _init           const   __cce_nalpha, _regex?._cce_nalpha?
    _init           const   __cce_ncntrl, _regex?._cce_ncntrl?
    _init           const   __cce_ndigit, _regex?._cce_ndigit?
    _init           const   __cce_ngraph, _regex?._cce_ngraph?
    _init           const   __cce_nlower, _regex?._cce_nlower?
    _init           const   __cce_nprint, _regex?._cce_nprint?
    _init           const   __cce_npunct, _regex?._cce_npunct?
    _init           const   __cce_nspace, _regex?._cce_nspace?
    _init           const   __cce_nblank, _regex?._cce_nblank?
    _init           const   __cce_nupper, _regex?._cce_nupper?
    _init           const __cce_nxdigit, _regex?._cce_nxdigit?
    _call           _advance_stream, ~ _stream, ~ _constant?._lbrack?, ~ _constant?._empty?
    _call           _bitset?._declare?, ~ _result
    setz            _negate
    cmp             (_stream and _constant?._byte_mask?), _constant?._caret?
    jno             _regex_lone_ccl_iterate
    _call           _advance_stream, ~ _stream, ~ _constant?._caret?, ~ _constant?._empty?
    not             _negate
   _regex_lone_ccl_iterate:
    check           ((_stream = _constant?._nullstr?) |\
                      ((_stream and _constant?._byte_mask?) = _constant?._rbrack?))
    jyes            _regex_lone_ccl_create
    compute         _slice, (_stream and ((1H shl (9H shl 3H)) - 1H))
    cmp             _slice, "[:alnum:]"
    arrange         _posix, __cce_alnum
    jyes            _regex_lone_ccl_posix
    cmp             _slice, "[:alpha:]"
    arrange         _posix, __cce_alpha
    jyes            _regex_lone_ccl_posix
    cmp             _slice, "[:cntrl:]"
    arrange         _posix, __cce_cntrl
    jyes            _regex_lone_ccl_posix
    cmp             _slice, "[:digit:]"
    arrange         _posix, __cce_digit
    jyes            _regex_lone_ccl_posix
    cmp             _slice, "[:graph:]"
    arrange         _posix, __cce_graph
    jyes            _regex_lone_ccl_posix
    cmp             _slice, "[:lower:]"
    arrange         _posix, __cce_lower
    jyes            _regex_lone_ccl_posix
    cmp             _slice, "[:print:]"
    arrange         _posix, __cce_print
    jyes            _regex_lone_ccl_posix
    cmp             _slice, "[:punct:]"
    arrange         _posix, __cce_punct
    jyes            _regex_lone_ccl_posix
    cmp             _slice, "[:space:]"
    arrange         _posix, __cce_space
    jyes            _regex_lone_ccl_posix
    cmp             _slice, "[:blank:]"
    arrange         _posix, __cce_blank
    jyes            _regex_lone_ccl_posix
    cmp             _slice, "[:upper:]"
    arrange         _posix, __cce_upper
    jyes            _regex_lone_ccl_posix
    or              _slice, (_stream and (_constant?._byte_mask? shl (9H shl 3H)))
    cmp             _slice, "[:xdigit:]"
    arrange         _posix, __cce_xdigit
    jyes            _regex_lone_ccl_posix
    cmp             _slice, "[:^alnum:]"
    arrange         _posix, __cce_nalnum
    jyes            _regex_lone_ccl_posix    
    cmp             _slice, "[:^alpha:]"
    arrange         _posix, __cce_nalpha
    jyes            _regex_lone_ccl_posix
    cmp             _slice, "[:^cntrl:]"
    arrange         _posix, __cce_ncntrl
    jyes            _regex_lone_ccl_posix
    cmp             _slice, "[:^digit:]"
    arrange         _posix, __cce_ndigit
    jyes            _regex_lone_ccl_posix    
    cmp             _slice, "[:^graph:]"
    arrange         _posix, __cce_ngraph
    jyes            _regex_lone_ccl_posix
    cmp             _slice, "[:^lower:]"
    arrange         _posix, __cce_nlower
    jyes            _regex_lone_ccl_posix
    cmp             _slice, "[:^print:]"
    arrange         _posix, __cce_nprint
    jyes            _regex_lone_ccl_posix
    cmp             _slice, "[:^punct:]"
    arrange         _posix, __cce_npunct
    jyes            _regex_lone_ccl_posix
    cmp             _slice, "[:^space:]"
    arrange         _posix, __cce_nspace
    jyes            _regex_lone_ccl_posix
    cmp             _slice, "[:^blank:]"
    arrange         _posix, __cce_nblank
    jyes            _regex_lone_ccl_posix
    cmp             _slice, "[:^upper:]"
    arrange         _posix, __cce_nupper
    jyes            _regex_lone_ccl_posix
    or              _slice, (_stream and (_constant?._byte_mask? shl (00AH shl 3H)))
    cmp             _slice, "[:^xdigit:]"
    arrange         _posix, __cce_nxdigit
    jyes            _regex_lone_ccl_posix
    _call           _regex_char, _bound_1, ~ _stream
    cmp             (_stream and _constant?._byte_mask?), _constant?._hyphen?
    jyes            _regex_lone_ccl_range
    compute         _bound_2, _bound_1
    jump            _regex_lone_ccl_merge
   _regex_lone_ccl_range:
    _call           _advance_stream, ~ _stream, ~ _constant?._hyphen?
    _call           _regex_char, _bound_2, ~ _stream
   _regex_lone_ccl_merge:
    _asmcmd         =assert (__bound_1 <== __bound_2)
   _regex_lone_ccl_loop:
    check           (_bound_1 <= _bound_2)
    jno             _regex_lone_ccl_iterate
    arrange         _lookup_1, {_bound_1}
    _call           _bitset?._insert?, ~ _result, ~ _lookup_1
    inc             _bound_1
    jump            _regex_lone_ccl_loop
   _regex_lone_ccl_posix:
    _call           _advance_stream, ~ _stream, ~ _slice
    cmpz            _insensitive
    jyes            _regex_lone_ccl_union
    cmp             _slice, "[:lower:]"
    jyes            _regex_lone_ccl_warning
    cmp             _slice, "[:upper:]"
    jno             _regex_lone_ccl_union
   _regex_lone_ccl_warning:
    _asmcmd         =display "regex warning: [:lower:] or [:upper:] used in ignore case option.", 00AH
   _regex_lone_ccl_union:
    _call           _bitset?._union?, ~ _result, ~ _posix
    jump            _regex_lone_ccl_iterate
   _regex_lone_ccl_create:
    cmpz            _negate
    jyes            _regex_lone_ccl_finish
    _call           _bitset?._negate_byte?, ~ _result
   _regex_lone_ccl_finish:
    _call           _advance_stream, ~ _stream, ~ _constant?._rbrack?, ~ _constant?._empty?
  end calminstruction
 
  calminstruction _regex_full_ccl? _result?*, _insensitive?*, _stream?*
    local           _range_1, _range_2, _slice, _return
    _init           var const  _diff, "{-}"
    _init           var const _union, "{+}"
    _init           var const _inter, "{&}"
    _call           _unique, _range_1, ccl
    _call           _unique, _range_2, * ccl
    _call           _regex_lone_ccl, ~ _range_1, ~ _insensitive, ~ _stream
   _regex_full_ccl_loop:
    compute         _slice, (_stream and ((1H shl (3H shl 3H)) - 1H))
    cmp             _slice, _diff
    jyes            _regex_full_ccl_operand
    cmp             _slice, _union
    jyes            _regex_full_ccl_operand
    cmp             _slice, _inter
    jno             _regex_full_ccl_convert
   _regex_full_ccl_operand:
    _call           _advance_stream, ~ _stream, ~ _slice
    _call           _regex_lone_ccl, ~ _range_2, ~ _insensitive, ~ _stream
    cmp             _slice, _diff
    jyes            _regex_full_ccl_diff
    cmp             _slice, _union
    jyes            _regex_full_ccl_union
    _call           _bitset?._intersection?, ~ _range_1, ~ _range_2
    jump            _regex_full_ccl_destroy
   _regex_full_ccl_diff:
    _call           _bitset?._difference?, ~ _range_1, ~ _range_2
    jump            _regex_full_ccl_destroy
   _regex_full_ccl_union:
    _call           _bitset?._union?, ~ _range_1, ~ _range_2
   _regex_full_ccl_destroy:
    _call           _bitset?._destroy?, ~ _range_2
    jump            _regex_full_ccl_loop
   _regex_full_ccl_convert:
    _call           _bitset?._empty?, _return, ~ _range_1
    cmpz            _return
    jyes            _regex_full_ccl_translate
    _call           _automata?._transition?, ~ _result, ~ _regex?._state_1?, ~ _constant?._empty?, ~ _regex?._state_2?
    _asmcmd         =display "regex warning: empty character class set", 00AH
    jump            _regex_full_ccl_finish
   _regex_full_ccl_translate:
    _bitset_foreach _range_1, _item
     _call          _regex_apply_isensitive, ~ _result, ~ _insensitive, ~ _item
    _end            _foreach
   _regex_full_ccl_finish:
    _call           _bitset?._destroy?, ~ _range_1
  end calminstruction

  calminstruction _regex_string? _result?*, _insensitive?*, _stream?*
    local       _temporary, _symbol, _initialize
    _call       _automata?._skeleton?, ~ _result
    _call       _automata?._transition?, ~ _result, ~ _regex?._state_1?, ~ _constant?._empty?, ~ _regex?._state_2?
    setz        _initialize
    _call       _advance_stream, ~ _stream, ~ _constant?._dquote?, ~ _constant?._empty?
    _call       _unique, _temporary, strlit
   _regex_string_iterate:
    cmp         _stream, _constant?._nullstr?
    jno         _regex_string_condition
    _asmcmd     =err "regex: regex string not terminated"
    jump        _regex_string_finish
   _regex_string_condition:
    cmp         (_stream and _constant?._byte_mask?), _constant?._dquote?
    jyes        _regex_string_finish
    _call       _automata?._skeleton?, ~ _temporary
    _call       _regex_symbol, ~ _temporary, ~ _insensitive, ~ _stream
    cmpz        _initialize
    jyes        _regex_string_copy
    _call       _automata?._thompson_concat?, ~ _result, ~ _temporary
    jump        _regex_string_destroy
   _regex_string_copy:
    not         _initialize
    _call       _automata?._duplicate?, ~ _result, ~ _temporary
   _regex_string_destroy:
    _call       _automata?._destroy?, ~ _temporary
    jump        _regex_string_iterate
   _regex_string_finish:
    _call       _advance_stream, ~ _stream, ~ _constant?._dquote?, ~ _constant?._empty?
  end calminstruction

  calminstruction _regex_option?: _result?*, _stream?*
    local       _destination, _current, _insensitive, _whatsoever, _ignore, _target
    _cstwrp     _insensitive
    _cstwrp     _whatsoever
    _cstwrp     _ignore
    _init       var const _igcase, "i"
    _init       var const _dotall, "s"
    _init       var const _skipws, "x"
    _init       var const _invert, "-"
    take        _destination, _result
    push        var _insensitive, _constant?._false?
    push        var _whatsoever, _constant?._false?
   _regex_option_loop:
    compute     _current, (_stream and _constant?._byte_mask?)
    check       ((_current = _igcase) | (_current = _dotall) | (_current = _skipws))
    jno         _regex_option_invert
    _call       _advance_stream, ~ _stream, ~ _current, ~ _constant?._empty?
    cmp         _current, _igcase
    arrange     _target, __insensitive
    jyes        _regex_option_update
    cmp         _current, _dotall
    arrange     _target, __whatsoever
    jyes        _regex_option_update
    arrange     _target, __ignore
   _regex_option_update:
    publish     _target, _constant?._true?
    jump        _regex_option_loop
   _regex_option_invert:
    cmp         _current, _invert
    jno         _regex_option_continue
    _call       _advance_stream, ~ _stream, ~ _invert, ~ _constant?._empty?
   _regex_option_loop_invert:
    compute     _current, (_stream and _constant?._byte_mask?)
    check       ((_current = _igcase) | (_current = _dotall) | (_current = _skipws))
    jno         _regex_option_continue
    _call       _advance_stream, ~ _stream, ~ _current, ~ _constant?._empty?
    cmp         _current, _igcase
    arrange     _target, __insensitive
    jyes        _regex_option_update_invert
    cmp         _current, _dotall
    arrange     _target, __whatsoever
    jyes        _regex_option_update_invert
    arrange     _target, __ignore
   _regex_option_update_invert:
    publish     _target, _constant?._false?
    jump        _regex_option_loop_invert
   _regex_option_continue:
    _call       _advance_stream, ~ _stream, ~ _constant?._colon?, ~ _constant?._empty?
    call        _regex_union?, _destination, _insensitive, _whatsoever, _stream
   _regex_option_finish:
    pop         _destination, _insensitive, _whatsoever
  end calminstruction

  calminstruction _regex_dot? _result?*, _dotall?*
    _repeat     _constant?._byte?, _index:0H
      cmp       _dotall, _constant?._true?
      jyes      _regex_dot_insert
      cmp       _index, 00AH
      _jyesnext
     _regex_dot_insert:
      _call     _automata?._transition?, ~ _result, ~ _regex?._state_1?, ~ _index, ~ _regex?._state_2?
    _end        _repeat
  end calminstruction

  calminstruction _regex_comment? _result?*, _stream?*
    local       _symbol
   _regex_comment_loop:
    _call       _regex_char, _symbol, ~ _stream
    cmp         _symbol, _constant?._rparen?
    jno         _regex_comment_loop
    _call       _automata?._transition?, ~ _result, ~ _regex?._state_1?, ~ _constant?._empty?, ~ _regex?._state_2?
  end calminstruction

  calminstruction _regex_atom?: _result?*, _insensitive?*, _whatsoever?*, _stream?*
    local       _current, _input, _destination, _index, _symbol, _igcase, _dotall, _slice
    _init       var const _comment, "(?#"
    _init       var const _option, "(?"
    _init       const _error, "regex: parsing error"
    take        _destination, _result
    take        _igcase, _insensitive
    take        _dotall, _whatsoever
    cmp         (_stream and 0FFFFFFH), _comment
    jyes        _regex_atom_instantiate
    cmp         (_stream and 0FFFFH), _option
    jyes        _regex_atom_option
    compute     _current, (_stream and _constant?._byte_mask?)
    cmp         _current, _constant?._dquote?
    jyes        _regex_atom_string
    cmp         _current, _constant?._lparen?
    jyes        _regex_atom_nested
    cmp         _current, _constant?._lbrace?
    jyes        _regex_atom_bound
   _regex_atom_instantiate:
    _call       _automata?._skeleton?, ~ _destination
    cmp         (_stream and 0FFFFFFH), _comment
    jyes        _regex_atom_comment
    cmp         _current, _constant?._lbrack?
    jyes        _regex_atom_ccl
    cmp         _current, _constant?._dot?
    jyes        _regex_atom_dot
    _call       _regex_symbol, ~ _destination, ~ _igcase, ~ _stream
    jump        _regex_atom_finish
   _regex_atom_string:
    _call       _regex_string, ~ _destination, ~ _igcase, ~ _stream
    jump        _regex_atom_finish
   _regex_atom_bound:
    _call       _regex_brace, ~ _destination, ~ _stream, ~ _regex?._brace_alias?
    jump        _regex_atom_finish
   _regex_atom_ccl:
    _call       _regex_full_ccl, ~ _destination, ~ _igcase, ~ _stream
    jump        _regex_atom_finish
   _regex_atom_nested:
    _call       _advance_stream, ~ _stream, ~ _constant?._lparen?
    call        _regex_union?, _destination, _igcase, _dotall, _stream
    _call       _advance_stream, ~ _stream, ~ _constant?._rparen?, ~ _error
    jump        _regex_atom_finish
   _regex_atom_comment:
    _call       _advance_stream, ~ _stream, ~ _comment, ~ _constant?._empty?
    _call       _regex_comment, ~ _destination, ~ _stream
    jump        _regex_atom_finish
   _regex_atom_option:
    _call       _advance_stream, ~ _stream, ~ _option, ~ _constant?._empty?
    _call       _regex_option, ~ _destination, ~ _stream
    _call       _advance_stream, ~ _stream, ~ _constant?._rparen?, ~ _error
    jump        _regex_atom_finish
   _regex_atom_dot:
    _call       _advance_stream, ~ _stream, ~ _constant?._dot?, ~ _constant?._empty?
    _call       _regex_dot, ~ _destination, ~ _dotall
   _regex_atom_finish:
    pop         _destination, _igcase, _dotall
  end calminstruction

  calminstruction _regex_closure?: _result?*, _insensitive?*, _whatsoever?*, _stream?*
    local       _return, _current, _input, _destination, _igcase, _dotall
    take        _destination, _result
    take        _igcase, _insensitive
    take        _dotall, _whatsoever
    _call       _regex_atom, ~ _destination, ~ _igcase, ~ _dotall, ~ _stream
   _regex_closure_initialise:
    compute     _input, _stream
   _regex_closure_loop:
    compute     _current, (_input and _constant?._byte_mask?)
    cmp         _current, _constant?._lbrace?
    jyes        _regex_closure_sequence
    cmp         _current, _constant?._star?
    jyes        _regex_closure_kleene
    cmp         _current, _constant?._plus?
    jyes        _regex_closure_positive
    cmp         _current, _constant?._question?
    jno         _regex_closure_finish
   _regex_closure_optional:
    _call       _automata?._emulate_optional?, ~ _destination
    jump        _regex_closure_update
   _regex_closure_positive:
    _call       _automata?._emulate_positive?, ~ _destination
    jump        _regex_closure_update
   _regex_closure_kleene:
    _call       _automata?._thompson_closure?, ~ _destination
   _regex_closure_update:
    shr         _input, 8H
    jump        _regex_closure_loop
   _regex_closure_sequence:
    compute     _current, ((_input shr 8H) and _constant?._byte_mask?)
    _call       _sanitize_digit, _return, ~ _current, ~ _constant?._base_decimal?
    check       (_return < 0H)
    jyes        _regex_closure_finish
    _call       _regex_brace, ~ _destination, ~ _stream, ~ _regex?._brace_sequence?
    jump        _regex_closure_initialise
   _regex_closure_finish:
    str         _input
    publish     _stream, _input
    pop         _destination, _igcase, _dotall
  end calminstruction
 
  calminstruction _regex_cat?: _result?*, _insensitive?*, _whatsoever?*, _stream?*
    local       _current, _temporary, _destination, _merge, _igcase, _dotall
    take        _destination, _result
    take        _igcase, _insensitive
    take        _dotall, _whatsoever
    _call       _unique, _temporary, cat
    push        _merge, _temporary
    _call       _regex_closure, ~ _destination, ~ _igcase, ~ _dotall, ~ _stream
   _regex_cat_loop:
    cmp         _stream, _constant?._nullstr?
    jyes        _regex_cat_finish
    compute     _current, (_stream and _constant?._byte_mask?)
    cmp         _current, _constant?._rparen?
    jyes        _regex_cat_finish
    cmp         _current, _constant?._pipe?
    jyes        _regex_cat_finish
    _call       _automata?._declare?, ~ _merge
    _call       _regex_closure, ~ _merge, ~ _igcase, ~ _dotall, ~ _stream
    _call       _automata?._thompson_concat?, ~ _destination, ~ _merge
    _call       _automata?._destroy?, ~ _merge
    jump        _regex_cat_loop
   _regex_cat_finish:
    pop         _destination, _igcase, _dotall, _merge
  end calminstruction

  calminstruction _regex_union?: _result?*, _insensitive?*, _whatsoever?*, _stream?*
    local       _temporary, _merge, _destination, _igcase, _dotall
    take        _destination, _result
    take        _igcase, _insensitive
    take        _dotall, _whatsoever
    _call       _unique, _temporary, union
    push        _merge, _temporary
    _call       _regex_cat, ~ _destination, ~ _igcase, ~ _dotall, ~ _stream
   _regex_union_loop:
    cmp         (_stream and _constant?._byte_mask?), _constant?._pipe?
    jno         _regex_union_finish
    _call       _advance_stream, ~ _stream, ~ _constant?._pipe?, ~ _constant?._empty?
    _call       _automata?._declare?, ~ _merge
    _call       _regex_cat, ~ _merge, ~ _igcase, ~ _dotall, ~ _stream
    _call       _automata?._thompson_union?, ~ _destination, ~ _merge
    _call       _automata?._destroy?, ~ _merge
    jump        _regex_union_loop
   _regex_union_finish:
    pop         _destination, _igcase, _dotall, _merge
  end calminstruction

  calminstruction _compile? _result?*, _expression?*
    local       _temporary
    _call       _unique, _temporary, compile
    str         _expression
    publish     _temporary, _expression
    arrange     _result, _result.=machine?
    _call       _regex_union, ~ _result, ~ _constant?._zero?, ~ _constant?._zero?, ~ _temporary
    cmp         _temporary, _constant?._nullstr?
    jyes        _compile_finish
    _asmcmd     =err "regex: parsing error"
   _compile_finish:
  end calminstruction

  calminstruction _connect? _result?*, _regexs?*&
    local           _return, _holder, _reverse, _list, _last, _item, _bookmark, _regex
    empty           _reverse
    empty           _list
    _iterate        _regex, _regexs
      arrange       _list, _list,_regex.=machine?
      arrange       _reverse, _regex,_reverse
    _end            _iterate
    _front          _list, =,
    arrange         _holder, _result.=machine?
    _call           _automata?._connect?, ~ _holder, ~ _list
    arrange         _holder, _result.=machine?.=accept?
    _bitset_foreach reverse _holder, _item,,_last
      cmpz          _last
      _jnoexit
      match         _regex=,_reverse?, _reverse
      arrange       _bookmark, _result.=table?._item?
      arrange       _regex, _regex.=meta?
      _call         _regex_meta_duplicate, ~ _bookmark, ~ _regex
    _end            _foreach
    _call           _bitset?._element?, _return, ~ _holder, ~ _constant?._zero?
    arrange         _bookmark, _result.=table?._return?
    arrange         _result, _result.=meta?
    _call           _regex_meta_duplicate, ~ _bookmark, ~ _result
  end calminstruction

  calminstruction _alias? _result?*, _expression?*
    symnum      _result
    arrange     _result, __bound?.=_#_result?
    _call       _declare, ~ _result, ~ _constant?._zero?, ~ _regex?._brace_alias?
    _call       _compile, ~ _result, ~ _expression
  end calminstruction

  calminstruction _generate_lookup? _module?*, _regex?*
    local           _holder, _virtual, _column, _size, _destination, _index, _count, _item, _last, _enum, _skip
    _init           const __module, _module
    _init           const __virtual, _virtual
    _init           const __column, _column
    _init           const __destination, _destination
    _init           const __size, _size
    stringify       _module
    _asmcmd         =db 00AH, __module, "::"
    arrange         _holder, _regex.=machine?
    call            _automata?._subset_construction?, __virtual, _holder
    _asmcmd         =db 00AH, 00AH, "; [TOKEN]", 00AH
    arrange         _holder, _regex.=machine?.=accept?
    setz            _enum
    _bitset_foreach _holder, _item
      _asmcmd       =db 00AH, ".", _regex.=table?._item?.=tokenname?, " = "
      compute       _destination, _enum
      numstr        _destination
      inc           _enum
      _asmcmd       =db __destination
    _end            _foreach
    compute         _destination, (_enum + 0H)
    numstr          _destination
    _asmcmd         =db 00AH, ".ERROR = ", __destination
    compute         _destination, (_enum + 1H)
    numstr          _destination
    _asmcmd         =db 00AH, ".EOF = ", __destination
    _asmcmd         =db 00AH, 00AH, "._state_table:"
    arrange         _size, _virtual.=_state_table.=sizeof
    varrfsh         _size
    shr             _size, 8H
    _repeat         _size, _index:0H
      _asmcmd       =load __column : 100H =from _virtual:(_virtual.=_state_table+(_index =shl 8H))
      _asmcmd       =db 00AH, "db "
      _repeat       100H, _count
        compute     _destination, (_column and 0FFH)
        shr         _column, 8H
        numstr      _destination
        _asmcmd     =db __destination
        cmp         _count, 100H
        _jyesnext
        _asmcmd     =db ","
      _end          _repeat
    _end            _repeat
    _asmcmd         =db 00AH
    _bitset_foreach _holder, _item
      arrange       _size, _regex.=table?._item?.=tokenname?
      compute       _size, lengthof(_size)
      numstr        _size
      _asmcmd       =db 00AH, "._string.", _regex.=table?._item?.=tokenname?,\
                      ":", " db ", __size, ", """, _regex.=table?._item?.=tokenname?, """"
    _end            _foreach
    _asmcmd         =db 00AH, "._string.ERROR: db 5, ""ERROR"""
    _asmcmd         =db 00AH, "._string.EOF: db 3, ""EOF"""
    _asmcmd         =db 00AH, "._string_table: ; [DEBUG]", 00AH, "dd "
    _bitset_foreach _holder, _item,, _last
      _asmcmd       =db "._string.", _regex.=table?._item?.=tokenname?, ", "
    _end            _foreach
    _asmcmd         =db "._string.ERROR, ._string.EOF"
    _asmcmd         =db 00AH, 00AH, "._accept_table:"
    arrange         _size, _virtual.=_accept_table.=sizeof
    varrfsh         _size
    shr             _size, 3H
    _repeat         _size, _index:0H
      _asmcmd       =load __column : 8H =from _virtual:(_virtual.=_accept_table+(_index =shl 3H))
      _asmcmd       =db 00AH, "db "
      compute       _destination, (_column and 0FFH)
      numstr        _destination
      _asmcmd       =db __destination
      shr           _column, 020H
      _asmcmd       =db ", .", _regex.=table?._column?.=tokenname?
    _end            _repeat
    _asmcmd         =db 00AH, "db 0"
    _asmcmd         =db 00AH, "._accept_table.size = (($ - ._accept_table) shr 1H)"
    _asmcmd         =db 00AH, 00AH, "._skip_table:"
    _bitset_foreach _holder, _item
      arrange       _skip, _regex.=table?._item?.=skippable?     
      varrfsh       _skip
      cmpz          _skip
      _jyesnext
      _asmcmd       =db 00AH, "db .", _regex.=table?._item?.=tokenname?
    _end            _foreach
    _asmcmd         =db 00AH, "db 0"
    _asmcmd         =db 00AH, "._skip_table.size = ($ - ._skip_table)"
  end calminstruction
end namespace
