
include "xcalm.alm"
include "bitset.inc"
include "automata.inc"
include "regex.inc"

;_automata?._skeleton? a1
;_automata?._transition? a1, {0H}, 'A', {1H}
;_automata?._thompson_concat? a1, a1
;_automata?._display? a1

_regex?._declare? _register, _constant?._false?
_regex?._compile? _register, "eax|ebx|ecx|edx|edi|esi|esp|ebp"

;_regex?._regex_meta_duplicate? _, _TEST.meta?

;_listing? = _constant?._false?
;calminstruction abc?
;  arrange _stream,
;  _iterate _item*, _stream
;  _end _iterate
;end calminstruction
;abc
;_listing? = _constant?._false?

;display _liststr?

