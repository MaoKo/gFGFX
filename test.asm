
virtual at 0H
  include "token_c.inc"
end virtual

virtual at 0H
_raw:: file "test.c"
_size = ($ - $$)
end virtual

macro _restore_state? _start?*, _last?*, _backup?*, _token?*, _count?*, _stream?*
    local _size, _symbol
    if (_start = 0H) ; reach DEAD state
        if (_last = 0H)
            error "lexing error"
            break
        end if
        load _offset:4H from token_c:(token_c._string_table + (_token shl 2H))
        load _size:byte from token_c:_offset
        load _symbol:_size from token_c:(_offset+1H)
        display _symbol, 00AH
        if ((_token = token_c.IDENTIFIER) | (_token = token_c.STRING) | (_token = token_c.COMMENT))
            load _lexeme:(_backup - _first) from _raw:_first
            display 01BH, "[31m", string(_lexeme), 00AH, 01BH, "[0m"
        end if
        _start = 1H
        _token = 0H
        _last = 0H
        _stream = _backup
        _first = _stream
    end if
end macro

_accept? := 0H
_index = 0H
while (not 0H)
    load _test:byte from token_c:(token_c._accept_table+(_index shl 1H))
    if (_test = 0H)
        break
    end if
    load _token:byte from token_c:((token_c._accept_table+(_index shl 1H))+1H)
    rept 1H _:_test
        _accept?._? = _token
    end rept
    _index = _index + 1H
end while

_source_c = 0H
_backup = ""
_count = 0H
_start = 1H
_last = 0H
_token = 0H
_first = _source_c

while (not 0H)
    rept 1H _:_start
        if (definite _accept?._?)
            _last = _start
            _backup = _source_c
            _token = _accept?._?
        end if
    end rept
    if (_source_c >= _size)
        break
    end if
    load _current:byte from _raw:_source_c
    load _start:byte from token_c:(token_c._state_table+((_start shl 8H) + _current))
    _source_c = _source_c + 1H
    _restore_state _start, _last, _backup, _token, _count, _source_c
end while
_start = 0H
_restore_state _start, _last, _backup, _token, _count, _source_c

