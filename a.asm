
include "xcalm.alm"
include "bitset.inc"
include "automata.inc"
include "regex.inc"

;_automata?._skeleton? a1
;_automata?._transition? a1, {0H}, 'A', {1H}
;_automata?._thompson_concat? a1, a1
;_automata?._display? a1

;_regex?._alias? LETTER, "[[:alpha:]_]"

_regex?._declare? _TEST, _constant?._false?
_regex?._compile? _TEST, "(?s:.)"
_automata?._display? _TEST.machine?

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

