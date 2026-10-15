import Velvet

/-!
# Tutorial 4: Interactive Proofs

`finish` won't always close everything. When it doesn't, you can see what's left, prove
that part yourself, or teach `grind` a lemma so it goes through automatically again.
-/

namespace Tut04

/-! ## What's left?

Integer square root, plus the claim that it's the *largest* such number. -/

method isqrt (n : Nat) returns (r : Nat)
  ensures lower: r * r ≤ n
  ensures largest: ∀ i, i * i ≤ n → i ≤ r
do
  let mut x : Nat := 0
  while loop_cond: (x + 1) * (x + 1) ≤ n
    invariant below: x * x ≤ n
    decreasing by_rem: n - x * x
  do
    x := x + 1
  return x

/-! `with finish` fails here, and the error says `case largest`. With `with try finish`,
whatever `finish` can't do is left for us, named after its clause.

The VC report shows how each goal was handled. -/

set_option velvet_vcgen.showVCReport true in
prove_correct isqrt by
  velvet_vcgen [isqrt] with try finish
  case largest =>
    -- The invariant and the loop exit are hypotheses, named `below` and `h_done_with`.
    intro i hi
    have : (x + 1) * (x + 1) ≤ i * i ∨ i ≤ x := by
      by_cases h : x + 1 ≤ i
      · exact .inl (Nat.mul_le_mul h h)
      · omega
    omega

/-! ## Teaching `grind` a lemma

The missing fact is that squaring is monotone. `grind` does linear arithmetic and doesn't
know that, so let's tell it. -/

theorem sq_le_sq {a b : Nat} (h : a ≤ b) : a * a ≤ b * b := Nat.mul_le_mul h h

/-! A plain `@[grind]` isn't enough here: `grind` wouldn't know when to use it.
`grind_pattern` says "whenever you see two squares `a * a` and `b * b`, try this". -/

grind_pattern sq_le_sq => a * a, b * b

-- Now the same method verifies with no manual proof.
set_option velvet.verifyOnDefinition true in
method isqrt' (n : Nat) returns (r : Nat)
  ensures lower: r * r ≤ n
  ensures largest: ∀ i, i * i ≤ n → i ≤ r
do
  let mut x : Nat := 0
  while loop_cond: (x + 1) * (x + 1) ≤ n
    invariant below: x * x ≤ n
    decreasing by_rem: n - x * x
  do
    x := x + 1
  return x

/-! Prefer the lemma when the same fact will come up again. Use a `case` proof when it's a
one-off. -/

end Tut04
