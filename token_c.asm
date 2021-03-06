
include "xcalm.alm"
;include "set.inc"
include "string.inc"
include "bitset.inc"
include "automata.inc"
include "regex.inc"
include "lexer.inc"
include "parser.inc"

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

macro decl_and_compile? _name?*, _expr?*, _skip?:_constant?._false?
    _regex?._declare? _name, _skip
    _regex?._compile? _name, _expr
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
decl_and_compile? COMMENT, "(//.*)|(/\*(\*+[^*/]|[^*])*\*+/)", _constant?._true?
decl_and_compile? SPACE, "[ \t\n]+", _constant?._true?

_regex?._connect? IDENTIFIER, INT_CONST, STRING, FLOAT_CONST, CHAR_CONST, STRING, LBRACK, RBRACK, LPAREN, RPAREN, LBRACE, RBRACE, DOT, ARROW, PLUSPLUS, MINUSMINUS, ANDB, STAR, PLUS, MINUS, TILDE, EXCLA, DIV, MOD, LSHIFT, RSHIFT, LESS, GREAT, LESSE, GREATE, EQ, NEQ, XOR, ORB, ORL, ANDL, QUES, COLON, SEMICOLON, ELLIP, ASSIGN, MULE, DIVE, MODE, PLUSE, MINE, LSHIFTE, RSHIFTE, ANDBE, XORE, ORBE, COMMA, BACK, DASH, DASHDASH, DLBRACK, DRBRACK, DLBRACE, DRBRACE, DDASH, DDASHDASH, COMMENT, SPACE
_regex?._generate_lookup? token_c, IDENTIFIER, _constant?._false?

