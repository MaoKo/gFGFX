
include "xcalm.alm"
;include "set.inc"
include "string.inc"
include "bitset.inc"
include "automata.inc"
include "regex.inc"
include "lexer.inc"
include "parser.inc"

;include "bootstrap.inc"
;include "token_c.inc"

;include "parser.lex"

;repeat 080H
;    _automata?._thompson_closure? _machine_1
;    _automata?._thompson_concat? _machine_1, _machine_2
;end repeat

;repeat 0FFFFH
;_automata?._subset_construction? _, _machine_1
;end repeat

;_machine_1 _automata?._display?

;_machine_1 _automata?._transition? {0},, {1}
;_machine_1 _automata?._transition? {0}, 'B'-'Z', {2}

;_machine_2 _automata?._duplicate? _machine_1
;_machine_1 _automata?._thompson_concat? _machine_2
;_machine_1 _automata?._finite_sequence? 1H, 3H
;_machine_1 _automata?._infinite_sequence? 2H
;_machine_1 _automata?._infinite_sequence? 2H
;_machine_1 _automata?._infinite_sequence? 2H
;_machine_1 _automata?._infinite_sequence? 2H

;_machine_1 _automata?._adjust? 1H
;_abc _automata?._duplicate? _machine_1
;_abc _automata?._display?

;_machine_2 _automata?._new_state? (not 0H), 0H
;_machine_2 _automata?._new_state? 0H, (not 0H)
;_machine_2 _automata?._transition? {0}, 'B', {1}

;_machine_3 _automata?._new_state? (not 0H), 0H
;_machine_3 _automata?._new_state? 0H, (not 0H)
;_machine_3 _automata?._transition? {0}, 'C', {1}

;_machine_1 _automata?._thompson_concat? _machine_3

;_abc _bitset?._declare?
;_abc _bitset?._insert? {0H}
;_machine_1 _automata?._display?
;_ _automata?._accept? 'O', _machine_1
;db _

;_machine_1 _automata?._display?
;_machine_2 _automata?._display?
;_machine_2 _automata?._adjust? 1H
;_machine_2 _automata?._display?
;_machine_1 _automata?._merge? _machine_2, 0H
;_machine_1 _automata?._display?

;_machine_4 _automata?._new_state? (not 0H), 0H
;_machine_4 _automata?._new_state? 0H, (not 0H)
;_machine_4 _automata?._transition? {0}, 'D', {1}

;_automata?._display? _machine_2
;_automata?._display? _machine_3
;_automata?._display? _machine_4

;_machine_1 _automata?._thompson_concat? _machine_3

;_machine_1 _automata?._thompson_union? _machine_4
;_machine_1 _automata?._thompson_closure?

;_automata?._display? _machine_1

;_abc _automata?._epsilon_closure? {0H}, _machine_1
;_set?._display? _abc

;_abc _automata?._accept? "DDDDDDABCD", _machine_1
;db _abc

;_regex?._declare? ABC
;_regex?._compile? ABC, "(?i:[a]{+}[0-9])bc" ; """a.[]""[ab]"
;_automata?._display? ABC.machine?
;_automata?._subset_construction? _, ABC.machine?

;_stream = "[abc]{-}[a]{&}[d]{+}[123]"
;_regex?._regex_full_ccl? _, 1H, _stream
;_automata?._display? _

;_grammar?._production? "<ABC>   -> <DEF> PIPE <I> | ;"

;_comment ~

_regex?._alias? LETTER, "[[:alpha:]_]"
_regex?._alias? DIGIT, "[[:digit:]]"
_regex?._alias? ESC_UNV, "(\\u[[:xdigit:]]{4}|\\U[[:xdigit:]]{8})"
_regex?._alias? ESC_OCT, "(\\[0-7]{1,3})"
_regex?._alias? ESC_HEX, "(\\x[[:xdigit:]]+)"
_regex?._alias? ESC_SEQ, "\\['""?\\abfnrtv]"
_regex?._alias? REG_ESCAPE, "({ESC_SEQ}|{ESC_OCT}|{ESC_HEX}|{ESC_UNV})"
_regex?._alias? DEC, "([1-9][[:digit:]]*)"
_regex?._alias? OCT, "(0[0-7]*)"
_regex?._alias? HEX, "(0[xX][[:xdigit:]]+)"
_regex?._alias? UNSIGN_SUFF, "[uU]"
_regex?._alias? LONG_SUFF, "[lL]"
_regex?._alias? LGLG_SUFF, "(ll|LL)"
_regex?._alias? INT_SUFF, "({UNSIGN_SUFF}{LONG_SUFF}?)|({UNSIGN_SUFF}{LGLG_SUFF})|({LONG_SUFF}{UNSIGN_SUFF}?)|({LGLG_SUFF}{UNSIGN_SUFF}?)"
_regex?._alias? SIGN, "[-+]"
_regex?._alias? FLOAT_SUFF, "[flFL]"
_regex?._alias? SCF_EXP, "[eE]{SIGN}?{DIGIT}+"
_regex?._alias? BIN_EXP, "[pP]{SIGN}?{DIGIT}+"
_regex?._alias? DEC_FRACT, "({DIGIT}+\.)|({DIGIT}+?\.{DIGIT}+)"
_regex?._alias? HEX_FRACT, "([[:xdigit:]]+\.)|([[:xdigit:]]+?\.[[:xdigit:]]+)"
_regex?._alias? DEC_FLOAT, "({DEC_FRACT}{SCF_EXP}?{FLOAT_SUFF}?)|({DIGIT}+{SCF_EXP}{FLOAT_SUFF}?)"
_regex?._alias? HEX_FLOAT, "0[xX]({HEX_FRACT}|[[:xdigit:]]){BIN_EXP}{FLOAT_SUFF}"

macro decl_and_compile? _name?*, _exp?*, _skip?:0H
    _regex?._declare? _name, _skip
    _regex?._compile? _name, _exp
end macro

decl_and_compile? IDENTIFIER, "({LETTER}|{ESC_UNV})({LETTER}|{DIGIT}|{ESC_UNV})*"
decl_and_compile? INT_CONST, "({DEC}|{OCT}|{HEX}){INT_SUFF}?"
decl_and_compile? FLOAT_CONST, "({DEC_FLOAT}|{HEX_FLOAT})"
decl_and_compile? CHAR_CONST, "[LuU]?'([^\n'\\]|{REG_ESCAPE})+'"
decl_and_compile? STRING, "(u8?|[UL])?\""([^\n""\\]|{REG_ESCAPE})*\"""
decl_and_compile? LBRACK, "\["
decl_and_compile? RBRACK, "]"
decl_and_compile? LPAREN, "\("
decl_and_compile? RPAREN, "\)"
decl_and_compile? LBRACE, "\{"
decl_and_compile? RBRACE, "}"
decl_and_compile? DOT, "\."
decl_and_compile? ARROW, "->"
decl_and_compile? PLUSPLUS, """++"""
decl_and_compile? MINUSMINUS, "--"
decl_and_compile? ANDB, "&"
decl_and_compile? STAR, "\*"
decl_and_compile? PLUS, "\+"
decl_and_compile? MINUS, "-"
decl_and_compile? TILDE, "\~"
decl_and_compile? EXCLA, "!"
decl_and_compile? DIV, "/"
decl_and_compile? MOD, "%"
decl_and_compile? LSHIFT, "<<"
decl_and_compile? RSHIFT, ">>"
decl_and_compile? LESS, "<"
decl_and_compile? GREAT, ">"
decl_and_compile? LESSE, "<="
decl_and_compile? GREATE, ">="
decl_and_compile? EQ, "=="
decl_and_compile? NEQ, "!="
decl_and_compile? XOR, "^"
decl_and_compile? ORB, "\|"
decl_and_compile? ORL, """||"""
decl_and_compile? ANDL, "&&"
decl_and_compile? QUES, "\?"
decl_and_compile? COLON, ":"
decl_and_compile? SEMICOLON, ";"
decl_and_compile? ELLIP, """..."""
decl_and_compile? ASSIGN, "="
decl_and_compile? MULE, "\*="
decl_and_compile? DIVE, "/="
decl_and_compile? MODE, "%="
decl_and_compile? PLUSE, "\+="
decl_and_compile? MINE, "-="
decl_and_compile? LSHIFTE, "<<="
decl_and_compile? RSHIFTE, ">>="
decl_and_compile? ANDBE, "&="
decl_and_compile? XORE, "^="
decl_and_compile? ORBE, "\|="
decl_and_compile? COMMA, ","
decl_and_compile? BACK, "\\"
decl_and_compile? DASH, "#"
decl_and_compile? DASHDASH, "##"
decl_and_compile? DLBRACK, "<:"
decl_and_compile? DRBRACK, ":>"
decl_and_compile? DLBRACE, "<%"
decl_and_compile? DRBRACE, "%>"
decl_and_compile? DDASH, "%:"
decl_and_compile? DDASHDASH, "%:%:"
decl_and_compile? COMMENT, "(//.*)|(/\*(\*+[^*/]|[^*])*\*+/)", (not 0H)
decl_and_compile? SPACE, "[ \t\n]+", (not 0H)

_regex?._connect? IDENTIFIER, INT_CONST, STRING, FLOAT_CONST, CHAR_CONST, STRING, LBRACK, RBRACK, LPAREN, RPAREN, LBRACE, RBRACE, DOT, ARROW, PLUSPLUS, MINUSMINUS, ANDB, STAR, PLUS, MINUS, TILDE, EXCLA, DIV, MOD, LSHIFT, RSHIFT, LESS, GREAT, LESSE, GREATE, EQ, NEQ, XOR, ORB, ORL, ANDL, QUES, COLON, SEMICOLON, ELLIP, ASSIGN, MULE, DIVE, MODE, PLUSE, MINE, LSHIFTE, RSHIFTE, ANDBE, XORE, ORBE, COMMA, BACK, DASH, DASHDASH, DLBRACK, DRBRACK, DLBRACE, DRBRACE, DDASH, DDASHDASH, COMMENT, SPACE
_regex?._generate_lookup? token_c, IDENTIFIER

;decl_and_compile? PLSG, "\+"
;decl_and_compile? MING, "-"
;decl_and_compile? DIVG, "/"
;decl_and_compile? STRG, "\*"
;decl_and_compile? EQG, "="
;decl_and_compile? LSSG, "<"
;decl_and_compile? GRTG, ">"
;decl_and_compile? LPRG, "\("
;decl_and_compile? RPRG, "\)"
;decl_and_compile? LBKG, "\["
;decl_and_compile? RBKG, "]"
;decl_and_compile? LBRG, "\{"
;decl_and_compile? RBRG, "}"
;decl_and_compile? CLG, ":"
;decl_and_compile? QUEG, "\?"
;decl_and_compile? ECLG, "!"
;decl_and_compile? COMG, ","
;decl_and_compile? DOTG, "\."
;decl_and_compile? PIPG, "\|"
;decl_and_compile? ANDG, "&"
;decl_and_compile? TLDG, "~"
;decl_and_compile? DSHG, "#"
;decl_and_compile? TCKG, "`"
;decl_and_compile? BSLG, "\\"
;decl_and_compile? COMG, ";.*"

;_regex?._alias? LETTER, "[[:alpha:]_]"
;_regex?._alias? DIGIT, "[[:digit:]]"
;_regex?._alias? IDENTIFIER, "{LETTER}({LETTER}|{DIGIT})*"
;_regex?._alias? BLANK, "[ \t]"
;decl_and_compile? NAME, "{IDENTIFIER}"
;decl_and_compile? REGEX, "{BLANK}*={BLANK}*.*\n+"
;decl_and_compile? ALIAS, "{BLANK}*:{BLANK}*.*\n+"
;decl_and_compile? LPAREN, "\("
;decl_and_compile? RPAREN, "\)"
;decl_and_compile? LANGLE, "<"
;decl_and_compile? RANGLE, ">"
;decl_and_compile? ATTRIBUTE, "@{IDENTIFIER}"
;decl_and_compile? SPACE, "{BLANK}+", (not 0H)

;_regex?._connect? NAME,REGEX,ALIAS,LPAREN,RPAREN,LANGLE,RANGLE,ATTRIBUTE,SPACE
;_regex?._generate_lookup? _lexerg, NAME

;virtual at 0H
;    include "token_c.lex"
;end virtual

;virtual at 0H
;_file:: file "test.c"
;.size = ($ - $$)
;end virtual

;while (not 0H)
;    _lexer?._get_next_token? token_c, _file, _file.size, _token, _lexeme, _debug
;    display "DEBUG = ", _debug, ", LEXEME ", 01BH, "[31m", _lexeme, 01BH, "[0m", 00AH
;    if (_token = token_c.EOF)
;        break
;    end if
;end while

;A = 1
;B = 2
;C = 3
;D = 4
;E = 5

;?if = 2
;then = 1
;?else = 5
;alpha = 6
;beta = 7

;_parser?._declare? _ABC
;_parser?._nonterminal? _ABC, (not 0H), <S>
;_parser?._nonterminal? _ABC, 0H, <L>
;_parser?._nonterminal? _ABC, 0H, <M>
;_parser?._productions? _ABC, <E> -> (A), (B), <A>, (D)
;_parser?._productions? _ABC, <E> -> (A), (B), <A>, (E)
;_parser?._productions? _ABC, <E> -> (A), (B), <A>
;_parser?._productions? _ABC, <E> -> (A), <A>

;_parser?._productions? _ABC, <S> -> (if), <E>, (then), <S> |\
;    (if), <E>, (then), <S>, (else), <S> |\
;    (alpha)
;_parser?._productions? _ABC, <E> -> (beta)
;_parser?._display? _ABC
;_parser?._left_factoring? _ABC

; <A> -> a b <N>
; <A> -> a b <B>
; <A> -> a <C>

;_parser?._nonterminal? _ABC, 0H, <F>
;_parser?._nonterminal? _ABC, 0H, <T>
;_parser?._productions? _ABC, <E> -> <E>, PLUS, <F> | <F>
;_parser?._productions? _ABC, <F> -> <F>, TIME, <T> | <T>
;_parser?._productions? _ABC, <T> -> LPAREN, <E>, RPAREN | ID
;_parser?._productions? _ABC, <S> -> <L>, (A), (A), (A), <M>
;_parser?._productions? _ABC, <L> -> <L>, <M> |
;_parser?._productions? _ABC, <M> -> <M>, <M> |
;_parser?._productions? _ABC, <A> -> <A>, alpha | beta
;_parser?._mark_nullable? _ABC
;_parser?._rules_out? _ABC, 0H, <E>
;_parser?._mark_nullable? _ABC
;db _ABC.nonterminal?.A.nullable?
;_parser?._chomsky_normal_form? _ABC
;_parser?._productions? _ABC, <_context?.#chomsky#1837> -> (A)
;_parser?._display? _ABC
;_parser?._immediate_left_recursion? _ABC
;_parser?._display? _ABC

;ZERO = 0H
;ONE = 1H
;TWO = 2H
;THREE = 3H
;FOUR = 4H
;FIVE = 5H
;SIX = 6H
;SEVEN = 7H
;EIGHT = 8H
;NINE = 9H
;PLUS = 00AH
;MINUS = 00BH
;E = 00CH
;DOT = 00DH

;_parser?._declare? Number
;_parser?._nonterminal? Number, (not 0H), <Number>
;_parser?._nonterminal? Number, 0H, <Integer>
;_parser?._nonterminal? Number, 0H, <Real>
;_parser?._nonterminal? Number, 0H, <Fraction>
;_parser?._nonterminal? Number, 0H, <Scale>
;_parser?._nonterminal? Number, 0H, <Digit>
;_parser?._nonterminal? Number, 0H, <Sign>
;_parser?._productions? Number, <Number> -> <Integer> | <Real>
;_parser?._productions? Number, <Integer> -> <Digit> | <Integer>, <Digit>
;_parser?._productions? Number, <Real> -> <Integer>, <Fraction>, <Scale> | <Integer>, <Fraction>
;_parser?._productions? Number, <Fraction> -> (DOT), <Integer>
;_parser?._productions? Number, <Scale> -> (E), <Sign>, <Integer>
;_parser?._productions? Number, <Digit> -> (ZERO) | (ONE) | (TWO) | (THREE) | (FOUR) | (FIVE) | (SIX) | (SEVEN) | (EIGHT) | (NINE)
;_parser?._productions? Number, <Sign> -> (PLUS) | (MINUS)
;_parser?._chomsky_normal_form? Number
;_parser?._display? Number

;repeat 010H
;_parser?._cyk_parsing? _result, _table, Number, 0H, THREE, TWO, DOT, FIVE, E, PLUS, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE  ; (32.5e+1)
;_parser?._cyk_derivation? _result, _table, Number, THREE, TWO, DOT, FIVE, E, PLUS, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE,     ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE
;end repeat

;LPAREN = 0H
;RPAREN = 1H
;EXCLA = 2H
;QUEST = 3H
;STR = 4H
;DEF = 5
;LLL = 6

;_parser?._declare? Query
;_parser?._nonterminal? Query, (not 0H), <Session>
;_parser?._nonterminal? Query, 0H, <Fact>
;_parser?._nonterminal? Query, 0H, <Question>
;_parser?._nonterminal? Query, 0H, <ABC>
;_parser?._nonterminal? Query, 0H, <GHI>
;_parser?._nonterminal? Query, 0H, <XYZ>
;_parser?._productions? Query, <Session> -> <Fact>, <Session>
;_parser?._productions? Query, <Session> -> <Question>
;_parser?._productions? Query, <Session> -> (LPAREN), <Session>, (RPAREN), <Session>
;_parser?._productions? Query, <Fact> -> (EXCLA), (STR)
;_parser?._productions? Query, <Question> -> (QUEST), (STR)
;_parser?._productions? Query, <ABC> -> (DEF) | ;
;_parser?._productions? Query, <GHI> -> <ABC>, (LLL) | (DEF), <GHI> ;
;_parser?._productions? Query, <XYZ> -> <GHI>, (DEF) ;
;_parser?._mark_first? Query
;_parser?._display? Query

;calminstruction abc?:
;    local           _lock, _i
;    _init           var _lock, (not 0H)
;    _init           var _i, 0H
;    inc             _i
; abc_loop:
;    _repeat 5H,     _index:0H
;        _asmcmd     =display "_i = ", (_i+030H), "_index = ", (_index+030H), 00AH
;        cmpz        _lock
;        setz        _lock
;        _jyesnext
;        call        abc
;    _end            _repeat
; abc_finish:
;    dec             _i
;end calminstruction

;calminstruction _abc?:
; _repeat 1H
;   call _abc
; _end _repeat
;end calminstruction
;_abc

;_abc 1,2,3

;_parser?._follow? _, Query, <GHI>
;_bitset?._display? _
;display DEF+030H, 00AH

;_parser?._cyk_parsing? _result, Number, (not 0H), ONE, ONE
;_parser?._cyk_parsing? _result, Number, (not 0H), ONE, ONE, ONE
;display _result+030H

;decl_and_compile? ABC, "(?abc)"
;match @, _
;load a:256 from @:@._state_table+0
;db a
;end match

;_automata?._display? IDENTIFIER.machine?
;db IDENTIFIER.table?.59?

;_automata?._declare? _machine_1
;_automata?._nstate? _machine_1, (not 0H), 0H
;_automata?._nstate? _machine_1, 0H, (not 0H)
;_automata?._transition? _machine_1, {0}, 'A', {1}

;_automata?._connect? _machine_1, SPACE.machine?
;_automata?._display? _machine_1

;_abc _regex?._declare?
;_abc _regex?._compile? "a{LETTER}"
;IDENTIFIER.machine? _automata?._display?

;repeat 050H
;repeat 100H
;    _ _automata?._epsilon_closure? {0H}, IDENTIFIER.machine?
;end repeat
;end repeat

;_ _regex?._declare?
;_ _regex?._compile? "(a|b)*abb"
;_ _regex?._compile? "[[:alpha:]_]"
;_.machine? _automata?._display?
;_abc _automata?._subset_construction? _.machine?
;repeat 0FF
;_abc _regex?._match? _, "abaaaaaaaaaaaababb"
;end repeat
;db _abc
;_stream = "{LETTER}"
;_ _regex?._declare?
;_ _regex?._regex_brace? _stream, ALIAS

;_ _regex?._compile? "([[:alpha]_]|(\\u[[:xdigit:]]{4}|\\U[[:xdigit:]]{8}))([[:alpha:]_]|(\\u[[:xdigit:]]{4}|\\U[[:xdigit:]]{8})|[[:digit:]])*"
;_automata?._display? _.machine?

;_machine_1 _automata?._new_state? (not 0H), 0H
;_machine_1 _automata?._new_state? 0H, (not 0H)
;_machine_1 _automata?._transition? {0}, 'A', {1}

;_automata?._display? _machine_1

;_machine_2 _automata?._new_state? (not 0H), 0H
;_machine_2 _automata?._new_state? 0H, (not 0H)
;_machine_2 _automata?._transition? {0}, 'B', {1}

;_machine_3 _automata?._new_state? (not 0H), 0H
;_machine_3 _automata?._new_state? 0H, (not 0H)
;_machine_3 _automata?._transition? {0}, 'C', {1}

;_machine_1 _automata?._connect? _machine_2, _machine_3

;_ _regex?._declare?
;_ _regex?._compile? "(a|b)*abb"
;_automata?._display? _.machine?
;_test _automata?._subset_construction? COMMENT.machine?

;_abc _automata?._declare?
;_def _automata?._duplicate? _abc

;_abc _automata?._new_state? (not 0H), 0H
;_abc _automata?._new_state? (not 0H), 0H
;_abc _automata?._new_state? 0H, (not 0H)

;_abc _automata?._transition? {0H}, 'a', {1H}
;_abc _automata?._transition? {0H}, 'b'-'h', {1H}
;_abc _automata?._transition? {0H},, {1H}
;_abc _automata?._transition? {0H}, 'c', {1H}
;_abc _automata?._transition? {0H}, 'c', {2H}
;_abc _automata?._transition? {0H}, 'z', {1H}
;_abc _automata?._transition? {1H}, 'p', {2H}
;_abc _automata?._transition? {2H}, 'p', {0H}

;_abc _automata?._display?
;_abc _automata?._adjust? 2H
;_abc _automata?._display?

;_abc.table?.0?.charset?.0? _bitset?._display?

;_abc _bitset?._declare?
;_abc _bitset?._inserts? {1,2,3}
;calminstruction (_result?) _def?
;  local _item
;  compute _item, 6H
;  _bitset_foreach reverse _result, _item, _first, _last
;    execute { display _item+"0" }
;    inc _item
;  _end _foreach
;end calminstruction
;_abc _def
;_abc _def

;repeat 0FFFFFH
;_ _bitset?._declare?
;_ _bitset?._insert? {1}
;_ _bitset?._insert? {5}
;_ _bitset?._insert? {4}
;_1 _bitset?._duplicate? _
;_1 _bitset?._union? {6,7,8}
;_2 _bitset?._duplicate? _1
;_2 _bitset?._union? {10,11}
;_2 _bitset?._intersection? _1
;end repeat

