
%%
LETTER          : [[:alpha:]_]
DIGIT           : [[:digit:]]
IDENTIFIER      : {LETTER}({LETTER}|{DIGIT})*
TERMINAL        = {IDENTIFIER}
NON_TERMINAL    = <{IDENTIFIER}>
ARROW           = ->
PIPE            = \|
DOT             = \.
LBRACE          = \{
LBRACK          = \[
RBRACE          = }
RBRACK          = ]
COMMENT @SKIP   = ;.*
BANK    @SKIP   = [ \t\n]+
%%
