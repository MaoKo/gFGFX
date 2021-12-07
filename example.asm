
include "xcalm.alm"
include "bitset.inc"
include "automata.inc"
include "regex.inc"

_regex?._declare? _register, _constant?._false?
_regex?._compile? _register, "xmm1" ; "(x|y|z)mm([0-9]|(1[0-9])|(2[0-9])|30|31)"

_regex?._match? _check, _register, "xmm1"
if (_check) 
  display "x86 Register Match"
end if

