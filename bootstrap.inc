
; TODO
%%
LETTER          : [[:alpha:]_]
DIGIT           : [[:digit:]]
IDENTIFIER      : {LETTER}({LETTER}|{DIGIT})*
BLANK           : [ \t] 
NAME            = {IDENTIFIER}
REGEX           = {BLANK}*={BLANK}*.*
ALIAS           = {BLANK}*:{BLANK}*.*
LPAREN          = \(
RPAREN          = \)
LANGLE          = <
RANGLE          = >
COMMA           = ,
ATTRIBUTE       = @{IDENTIFIER}
SPACE   @SKIP   = ({BLANK}|\n)+
COMMENT @SKIP   = ;.*
%%
