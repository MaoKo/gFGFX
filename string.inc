
_string? := 0H
namespace _string?
  calminstruction _declare? _result?*
    publish     _result, _constant?._nullstr?
  end calminstruction

  calminstruction _duplicate? _result?*, _string?*
    str         _string
    publish     _result, _string
  end calminstruction

  calminstruction _element? _result?*, _string?*, _position?*
    compute     _string, ((_string shr (_position shl 3H)) and 0FFH)
    publish     _result, _string
  end calminstruction

  calminstruction _insert? _result?*, _character?*
    local       _string
    _balance    _character, {}
    jno         _insert_finish
    compute     _string, string(_result)
    concatenate _string, _character
    publish     _result, _string
   _insert_finish:
  end calminstruction

  calminstruction _length? _result?*, _string?*
    compute     _string, lengthof(string(_string))
    publish     _result, _string
  end calminstruction

  _generate_foreach string, _declare?, _duplicate?, _element?, _insert?, _length?

  macro calminstruction?._head? _result?*, _string?*
    compute     _result, (_string and 0FFH)
  end macro

  macro calminstruction?._truncate_head? _result?*, _count?*
    shr         _result, (_count shl 3H)
    str         _result
  end macro

  macro calminstruction?._tail? _result?*, _string?*
    compute     _result, (_string shr ((lengthof(_string) - 1H) shl 3H))
  end macro

  macro calminstruction?._truncate_tail? _result?*, _count?*
    and         _result, ((1H shl ((lengthof(_result) - _count) shl 3H)) - 1H)
    str         _result
  end macro

  iterate _kind?*, head,tail
    calminstruction _remove_#_kind? _result?*, _chars?*&
      local                 _char, _current, _string, _change
      compute               _string, _result
     _remove_head_loop:
      setz                  _change
      _iterate              _char, _chars
        _#_kind             _current, _string
        cmp                 _current, _char
        _jnonext
        _truncate_#_kind    _string, 1H
        not                 _change
        _break
      _end                  _iterate
      cmpz                  _change
      jno                   _remove_head_loop
     _remove_head_finish:
      str                   _string
      publish               _result, _string
    end calminstruction
  end iterate

  iterate <_kind?*,_operator_1?*,_operator_2?>, _lower,or,, _upper,and,not
    calminstruction _kind? _result?*
      local             _char
      _string_foreach   _result, _char
        _operator_1     _char, (_operator_2 020H)
      _end              _foreach
    end calminstruction
  end iterate
end namespace

