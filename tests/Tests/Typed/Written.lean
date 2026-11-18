import Tests.Typed.Written.Records
import Tests.Typed.Written.Strcmp
import Tests.Typed.Written.Stack
import Tests.Typed.Written.Atoi
import Tests.Typed.Written.Ring
import Tests.Typed.Written.Bubble
import Tests.Typed.Written.Words
import Tests.Typed.Written.Half
import Tests.Typed.Written.Head
import Tests.Typed.Written.ReadFull
import Tests.Typed.Written.Digits
import Tests.Typed.Written.OrNull
import Tests.Typed.Written.Arena
import Tests.Typed.Written.RetLost

/-!
# Programs written as an author would, each needing something of the type checker

A table of records gone through by an index; a comparison of two texts
that returns nought or one; a stack of numbers kept in a region lent, its
count within bounds across calls; a number read from its digits; a ring of
bytes with its indices masked; a sort in place of a row that may be
written; words counted, the count's low byte the status; four bytes stored into a
number the program made, the number known still; a count chosen by a
conditional move; a function that moves its pointer through a buffer lent;
a number written out in digits, each byte stored known to be a digit and
what is written to standard output proved to be digits and an end of line; a
function that hands its caller a page, or nought; a function that carves a
piece off memory it is lent and gives back the rest; and, refused, a function
that stores over the address it returns to, the store named. Each is typed as
it is compiled.
-/
