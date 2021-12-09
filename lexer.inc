
_lexer? := 0H
namespace _lexer?
  virtual at 0H
    include "bootstrap.lex"
  end virtual

  _source = (not 0H)
  calminstruction _get_next_token_reset?
    compute     _source, (not 0H)
  end calminstruction
  calminstruction _get_next_token? _table?*, _virtual?*, _size?*, _token?*, _lexeme?*, _debug?
    local       _holder, _state, _last, _index, _extract, _value, _accept, _error, _eof, _backup, _begin, _offset, _length
    _cstwrp     _accept
    _cstwrp     _skip
    _cstwrp     gnxtk
    _init       const _empty,
    _init       var const _start, 1H
   _get_next_token_start:
    compute     _state, _start
    setz        _last
    compute     _begin, _source
    cmp         _source, (not 0H)
    jyes        _get_next_token_initialize
    check       (_source >= _size)
    jno         _get_next_token_transition
    publish     _token, _eof
    jump        _get_next_token_extract
   _get_next_token_initialize:
    setz        _source
    setz        _begin
    call        _unique, __accept, _gnxtk
    call        _unique, __skip, _gnxtk
    arrange     _error, _table.=ERROR
    varrfsh     _error
    arrange     _eof, _table.=EOF
    varrfsh     _eof
    setz        _index
   _get_next_token_skippable:
    ;loadvar     byte, _extract, <[_table]>:(<[_table]>._skip_table + _index)
    cmpz        _extract
    jyes        _get_next_token_register
    assign      _skip._extract, _empty
    inc         _index
    jump        _get_next_token_skippable
   _get_next_token_register:
    setz        _index
   _get_next_token_bookmark:
    ;loadvar     byte, _extract, <[_table]>:(<[_table]>._accept_table + (_index shl 1H))
    cmpz        _extract
    jyes        _get_next_token_transition
    ;loadsym     byte, _value, <[_table]>:(<[_table]>._accept_table + ((_index shl 1H) + 1H))
    assign      _accept._extract, _value
    inc         _index
    jump        _get_next_token_bookmark
   _get_next_token_transition:
    arrange     _holder, _accept._state
    transform   _holder
    jno         _get_next_token_advance
    compute     _last, _state
    compute     _backup, _source
    assign      _token, _holder
   _get_next_token_advance:
    check       (_source >= _size)
    jyes        _get_next_token_retreive
    ;loadvar     byte, _value, <[_virtual]>:<[_source]>
    ;loadvar     byte, _state, <[_table]>:(<[_table]>._state_table + (_state shl 8H) + (_value))
    inc         _source
    cmpz        _state ; reach dead state
    jno         _get_next_token_transition
   _get_next_token_retreive:
    cmpz        _last
    jno         _get_next_token_skip
    publish     _token, _error
    jump        _get_next_token_extract
   _get_next_token_skip:
    compute     _source, _backup
    arrange     _holder, _token
    reprnum     _holder
    arrange     _holder, _skip._holder
    transform   _holder
    jyes        _get_next_token_start
   _get_next_token_extract:
    loadstr     (_source - _begin), _holder, <[_virtual]>:<[_begin]>
    publish     _lexeme, _holder
    match       ,_debug
    jyes        _get_next_token_finish
    ;loadvar     dword, _offset, <[_table]>:(<[_table]>._string_table + (_token shl 2H))
    ;loadvar     byte, _length, <[_table]>:_offset
    ;loadstr     _length, _holder, <[_table]>:(_offset + 1H)
    publish     _debug, _holder
   _get_next_token_finish:
  end calminstruction

  define _symbol?
  define _module?
  calminstruction %%
    local   _source, _consistent, _state, _backup, _last, _token, _lexeme, _virtual, _length, _export, _alias, _skipping, _global, _trash
    _init   const __source, _source
    _init   const __virtual, _virtual
    _init   const __token, _token
    _init   const __lexeme, _lexeme
    _init   const _path, _lexer?.%%
    _init   const _%%, %%
    _init   const _bootstrap, bootstrap
    _init   const _blank, 020H, 009H
    ;_init   const _newline, 00AH
    _init   const _empty,
    _init   var const _skip, "@SKIP"
    _init   var const _push, "@PUSH"
    _init   var const _pop, "@POP"
    _init   var const _begin, "@BEGIN"
    _init   var _consistent, 0H
    cmp     _consistent, 0H
    jyes    _%%_catch_all
    call    _get_next_token_reset
    setz    _consistent
    setz    _global
    arrange _export,
    call    _unique, __virtual, _%%
    _asmcmd =eval "define _lexer?._module? ", =__file__
    match   _module=._trash?, _module
    _asmcmd =virtual =at 0H
    _asmcmd _virtual:: =db __source
    _asmcmd =end =virtual
    compute _length, lengthof(_source)
   _%%_loop:
    setz    _skipping
    call    _get_next_token, _bootstrap, _virtual, _length, __token, __lexeme, _empty
    cmp     _token, bootstrap.EOF
    jyes    _%%_build
    _asmcmd =assert (__token == =_lexer?.=bootstrap.=NAME)
    _asmcmd =eval "define _lexer?._symbol? ", __lexeme
    call    _get_next_token, _bootstrap, _virtual, _length, __token, __lexeme, _empty
    compute _alias, (not 0H)
    cmp     _token, bootstrap.ALIAS
    jyes    _%%_parse
    inc     _global
    setz    _alias
    arrange _export, _export,_symbol
    cmp     _token, bootstrap.ATTRIBUTE
    jno     _%%_declare
    call    _string?._upper?, __lexeme
    cmp     _lexeme, _skip
    jyes    _%%_skip
    nop     cmp _lexeme, _push 
    nop     cmp _lexeme, _pop
    nop     cmp _lexeme, _begin
    _asmcmd =err "lexer: attribute undefined"
    exit
   _%%_skip:
    not     _skipping
    call    _get_next_token, _bootstrap, _virtual, _length, __token, __lexeme, _empty
   _%%_declare:
    _asmcmd =assert (__token == =_lexer?.=bootstrap.=REGEX)
   _%%_parse:
    call    _string?._remove_head?, __lexeme, _blank
    shr     _lexeme, 8H
    call    _string?._remove_head?, __lexeme, _blank
    ;call    _string?._remove_tail?, __lexeme, _newline
    cmpz    _alias
    jno     _%%_alias
    call    _regex?._declare?, _symbol, _skipping, _empty
    call    _regex?._compile?, _symbol, _lexeme
   _%%_alias:
    call    _regex?._alias?, _symbol, _lexeme
    jump    _%%_loop
   _%%_build:
    _asmcmd =assert (_global > 0H)
    match   =,_global _export?, _export
    match   =,_export, _export
    jno     _%%_lookup
    call    _regex?._connect?, _global, _export
   _%%_lookup:
    call    _regex?._generate_lookup?, _module, _global
    jump    _%%_finish
   _%%_catch_all:
    compute _source, ""
    not     _consistent
    _asmcmd =retaincomments
    _asmcmd =calminstruction ?! =_line?&
    _asmcmd =stringify =_line
    _asmcmd =cmp =_line, "%%"
    _asmcmd =jyes =_catch_all_purge
    _asmcmd =concatenate __source, =_line
    _asmcmd =concatenate __source, 00AH
    _asmcmd =jump =_catch_all_finish
    _asmcmd =_catch_all_purge:
    _asmcmd =_asmcmd ===purge ?
    _asmcmd =_asmcmd ===removecomments
    _asmcmd =call _path
    _asmcmd =_catch_all_finish:
    _asmcmd =end =calminstruction
   _%%_finish:
  end calminstruction
end namespace

macro %%
    _lexer?.%%
end macro

