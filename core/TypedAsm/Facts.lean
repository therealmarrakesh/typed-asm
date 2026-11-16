import Lean

/-!
# Facts given to the checker

What a program computes is sometimes more than the checker can see: that a
product is the factorial of a number, say. A theorem marked `@[asm_fact]`
is a fact the checker may use for what it is left to show at the end of a
block, so that the block need not be typed by hand for the sake of one
equation. The facts are used as `simp` uses its lemmas, together with what
is known where the block is typed.
-/

/-- Facts about what a program computes, for the checker to use where it is
left to show that a value is the one a context asks for. -/
register_simp_attr asm_fact
