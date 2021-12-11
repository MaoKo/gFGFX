
include "xcalm.alm"
;include "set.inc"
include "string.inc"
include "bitset.inc"
include "automata.inc"
include "regex.inc"
include "lexer.inc"
include "parser.inc"

;macro decl_and_compile? _name?*, _expr?*, _skip?:_constant?._false?
;    _regex?._declare? _name, _skip
;    _regex?._compile? _name, _expr
;end macro

;decl_and_compile? A, "A"
;decl_and_compile? B, "B"

;_regex?._connect? A, B
;_regex?._generate_lookup? test, A, _constant?._false?

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

;_bitset?._declare? _bt
;_bitset?._insert? _bt, {1H}
;_bitset?._declare? _abc
;_bitset?._insert? _abc, {2H}
;_bitset?._cache_retreive_object? _bt, _suc, _test_1, _bt
;_bitset?._cache_insert_object? _test_1, _bt, _abc

;_bitset?._cache_insert? _test_1, {1H}, ABC
;_bitset?._cache_insert? _test_2, {1H}, DEF
;_bitset?._cache_retreive? _ret, _suc, _test_1, {1H}
;_bitset?._cache_clear? *

;_regex?._declare? _register, _constant?._false?
;_regex?._compile? _register, "(x|y|z)mm([0-9]|(1[0-9])|(2[0-9])|30|31)"
;repeat 0FFFFH
;_regex?._match? _check, _register, "xmm1ddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
;end repeat

;A? = 3
;B? = 5
;D? = 6

;_parser?._declare? _ABC
;_parser?._nonterminal? _ABC, _constant?._true?, <S>
;_parser?._nonterminal? _ABC, _constant?._false?, <L>
;_parser?._nonterminal? _ABC, _constant?._false?, <M>
;_parser?._productions? _ABC, <L> -> (A), (B), <M>, (D)
;_parser?._productions? _ABC, <E> -> (A), (B), <A>, (E)
;_parser?._productions? _ABC, <E> -> (A), (B), <A>
;_parser?._productions? _ABC, <E> -> (A), <A>


;<D> -> <A>
;<A> -> <B>, (T), <B>
;<B> -> (C)|

