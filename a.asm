
include "xcalm.alm"
;include "set.inc"
include "string.inc"
include "bitset.inc"
include "automata.inc"
include "regex.inc"
include "lexer.inc"
include "parser.inc"

macro decl_and_compile? _name?*, _expr?*, _skip?:_constant?._false?
    _regex?._declare? _name, _skip
    _regex?._compile? _name, _expr
end macro

decl_and_compile? A, "A"
decl_and_compile? B, "B"

_regex?._connect? A, B
_regex?._generate_lookup? test, A

;_automata?._declare? a1
;_automata?._new_state? a1, _constant?._true?, _constant?._false?
;_automata?._new_state? a1, _constant?._false?, _constant?._false?
;_automata?._new_state? a1, _constant?._false?, _constant?._false?
;_automata?._display? a1
;_automata?._transition? a1, {0H}, 'A', {1H}
;_automata?._transition? a1, {0H}, 'B', {1H}
;_automata?._transition? a1, {0H}, 'C', {1H}
;_automata?._transition? a1, {0H}, 'D', {2H}
;_bitset?._display? a1.table?.0?.charall?

