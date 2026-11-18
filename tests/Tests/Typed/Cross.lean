import Tests.Typed.Saved
import Hello
import Sum
import Keep
import Lend
import Fact
import Buffer
import Echo
import Pick
import Lengths

/-!
# The compiled checker held against its definition

A program is checked by running the checker as compiled code. Here Lean's
kernel runs the same checker, by its definition, on some of the smaller
examples, and comes to the same answer: each of these is a program whose
own file has it checked by compiled code. And the compiled checker is run
on programs the tests before this have, as theorems of the kernel's,
refused: it refuses them too.

This is a test of the tool. Nothing an author does goes through it.
-/

open TypedAsm TypedAsm.U

namespace Tests.Cross

/-! ## Accepted by compiled code in their own files, and here by the kernel -/

example : wholeOk Hello.code .start 0 Hello.pg Hello.labels (needFuel Hello.pg Hello.labels [])
    = true := by decide +kernel

example : wholeOkWith Sum.code .start 1 [] Sum.blocks Sum.pg Sum.labels
    (needFuel Sum.pg Sum.labels []) = true := by decide +kernel

example : wholeOk Keep.code .start 3 Keep.pg Keep.labels (needFuel Keep.pg Keep.labels [])
    = true := by decide +kernel

example : wholeOk Lend.code .start 4 Lend.pg Lend.labels (needFuel Lend.pg Lend.labels [])
    = true := by decide +kernel

example : wholeOk Fact.code .start 11 Fact.pg Fact.labels (needFuel Fact.pg Fact.labels [])
    = true := by decide +kernel

example : wholeOk Buffer.code .start 2 Buffer.pg Buffer.labels
    (needFuel Buffer.pg Buffer.labels []) = true := by decide +kernel

example : wholeOkWith Echo.code .start 0 [] Echo.blocks Echo.pg Echo.labels
    (needFuel Echo.pg Echo.labels []) = true := by decide +kernel

example : wholeOkWith Pick.code .start 0 [] Pick.blocks Pick.pg Pick.labels
    (needFuel Pick.pg Pick.labels []) = true := by decide +kernel

example : wholeOk Lengths.code .start 4 Lengths.pg Lengths.labels
    (needFuel Lengths.pg Lengths.labels []) = true := by decide +kernel

/-! ## Refused by the kernel in the tests before, and here by compiled code -/

open Tests.Saved in
#guard !wholeOk (code dropped) .start 2 (pg dropped) (labels dropped [.r12]) 40

open Tests.Saved in
#guard !wholeOk (code restored) .start 2 (pg restored) (labels restored []) 40

open Tests.Saved in
#guard !wholeOk kept .start 1 pgKept (keptLabels .any) 40

open Tests.Saved in
#guard wholeOk kept .start 1 pgKept (keptLabels (.val 7)) 40

end Tests.Cross
