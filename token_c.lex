
%%
LETTER          : [[:alpha:]_]
DIGIT           : [[:digit:]]
ESC_UNV         : (\\u[[:xdigit:]]{4}|\\U[[:xdigit:]]{8})
ESC_OCT         : (\\[0-7]{1,3})
ESC_HEX         : (\\x[[:xdigit:]]+)
ESC_SEQ         : \\['"?\\abfnrtv]
REG_ESCAPE      : ({ESC_SEQ}|{ESC_OCT}|{ESC_HEX}|{ESC_UNV})
DEC             : ([1-9][[:digit:]]*)
OCT             : (0[0-7]*)
HEX             : (0[xX][[:xdigit:]]+)
UNSIGN_SUFF     : [uU]
LONG_SUFF       : [lL]
LGLG_SUFF       : (ll|LL)
INT_SUFF        : ({UNSIGN_SUFF}{LONG_SUFF}?)|({UNSIGN_SUFF}{LGLG_SUFF})|({LONG_SUFF}{UNSIGN_SUFF}?)|({LGLG_SUFF}{UNSIGN_SUFF}?)
SIGN            : [-+]
FLOAT_SUFF      : [flFL]
SCF_EXP         : [eE]{SIGN}?{DIGIT}+
BIN_EXP         : [pP]{SIGN}?{DIGIT}+
DEC_FRACT       : ({DIGIT}+\.)|({DIGIT}+?\.{DIGIT}+)
HEX_FRACT       : ([[:xdigit:]]+\.)|([[:xdigit:]]+?\.[[:xdigit:]]+)
DEC_FLOAT       : ({DEC_FRACT}{SCF_EXP}?{FLOAT_SUFF}?)|({DIGIT}+{SCF_EXP}{FLOAT_SUFF}?)
HEX_FLOAT       : 0[xX]({HEX_FRACT}|[[:xdigit:]]){BIN_EXP}{FLOAT_SUFF}
IDENTIFIER      = ({LETTER}|{ESC_UNV})({LETTER}|{DIGIT}|{ESC_UNV})*
INT_CONST       = ({DEC}|{OCT}|{HEX}){INT_SUFF}?
FLOAT_CONST     = ({DEC_FLOAT}|{HEX_FLOAT})
CHAR_CONST      = [LuU]?'([^\n'\\]|{REG_ESCAPE})+'
STRING          = (u8?|[UL])?\"([^\n"\\]|{REG_ESCAPE})*\"
;LBRACK          = \[
;RBRACK          = ]
;LPAREN          = \(
;RPAREN          = \)
;LBRACE          = \{
;RBRACE          = }
;DOT             = \.
;ARROW           = ->
;PLUSPLUS        = "++"
;MINUSMINUS      = --
;ANDB            = &
;STAR            = \*
;PLUS            = \+
;MINUS           = -
;TILDE           = \~
;EXCLA           = !
;DIV             = /
;MOD             = %
;LSHIFT          = <<
;RSHIFT          = >>
;LESS            = <
;GREAT           = >
;LESSE           = <=
;GREATE          = >=
;EQ              = ==
;NEQ             = !=
;XOR             = ^
;ORB             = \|
;ORL             = "||"
;ANDL            = &&
;QUES            = \?
;COLON           = :
;SEMICOLON       = ;
;ELLIP           = "..."
;ASSIGN          = =
;MULE            = \*=
;DIVE            = /=
;MODE            = %=
;PLUSE           = \+=
;MINE            = -=
;LSHIFTE         = <<=
;RSHIFTE         = >>=
;ANDBE           = &=
;XORE            = ^=
;ORBE            = \|=
;COMMA           = ,
;DASH            = #
;DASHDASH        = ##
;DLBRACK         = <:
;DRBRACK         = :>
;DLBRACE         = <%
;DRBRACE         = %>
;DDASH           = %:
;DDASHDASH       = %:%:
;COMMENT @SKIP   = (//.*)|(/\*(\*+[^*/]|[^*])*\*+/)
;SPACE   @SKIP   = [ \t\n]+
%%
