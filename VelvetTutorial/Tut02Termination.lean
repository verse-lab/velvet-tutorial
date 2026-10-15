import Velvet

/-!
# Tutorial 2: Handling Termination

So far every method had to terminate (total correctness). Sometimes we can't prove that,
or don't care. *Partial correctness* only promises: if the method returns, the result is
right.
-/

namespace Tut02

open Lean.Order WPPartial

/-! ## Total correctness needs a measure

Nobody knows whether Collatz always reaches `1`, so there's no `decreasing` measure to
give, and Velvet refuses. -/

/--
error: `while` requires a `decreasing` clause in total correctness; add `decreasing <measure>` or use partial correctness
-/
#guard_msgs in
method collatzTotal (n : Nat) returns (res : Nat)
  requires pos: n > 0
  ensures one: res = 1
do
  let mut x := n
  while loop_cond: x ≠ 1
    invariant x_pos: x > 0
  do
    if x % 2 = 0 then
      x := x / 2
    else
      x := 3 * x + 1
  return x

/-! ## Partial correctness

Switch to partial mode and the measure isn't needed. If the loop exits, `x = 1`. -/

set_option velvet.semantics.termination "partial" in
method collatz (n : Nat) returns (res : Nat)
  requires pos: n > 0
  ensures one: res = 1
do
  let mut x := n
  while loop_cond: x ≠ 1
    invariant x_pos: x > 0
  do
    if x % 2 = 0 then
      x := x / 2
    else
      x := 3 * x + 1
  return x

prove_correct collatz by
  velvet_vcgen [collatz] with finish

/-- info: some 1 -/
#guard_msgs in
#eval collatz 27

-- Notice `termination_semantics : True` here, instead of `False`.
#check collatz.spec

/-! ## The catch

A loop that never exits satisfies any postcondition. This one returns `0`, yet we can
"prove" it returns `42`. -/

set_option velvet.semantics.termination "partial" in
method spin returns (res : Nat)
  ensures res = 42
do
  let mut i := 0
  while i ≥ 0
    invariant True
  do
    i := i + 1
  return 0

prove_correct spin by
  velvet_vcgen [spin] with finish

/-! ## Recursion by induction

Structural recursion terminates, so plain induction works. -/

method rec fact (n : Nat) returns (res : Nat)
  ensures pos: res > 0
do
  match n with
  | 0 => return 1
  | k + 1 =>
    let r ← fact k
    return (k + 1) * r

prove_correct fact by
  intro n
  induction n with
  | zero => unfold fact; velvet_vcgen with finish
  | succ k ih => unfold fact; velvet_vcgen with finish

/-- info: some 120 -/
#guard_msgs in
#eval fact 5

/-! ## Recursion by fixpoint induction

`nextPrime` does terminate, but proving it means proving there are infinitely many
primes. With partial correctness we can skip that. -/

def isPrime (n : Nat) : Bool :=
  n ≥ 2 && (List.range n).all (fun d => d < 2 || n % d ≠ 0)

set_option velvet.semantics.termination "partial" in
method rec nextPrime (k : Nat) returns (res : Nat)
  ensures prime: isPrime res = true
  ensures ge: res ≥ k
do
  if isPrime k then
    return k
  else
    nextPrime (k + 1)

/-- info: some 97 -/
#guard_msgs in
#eval nextPrime 90

/-! No induction on `k` here. Instead we use fixpoint induction, which has two steps.
This only works for partial correctness. -/

prove_correct nextPrime by
  intro k
  refine nextPrime.fixpoint_induct (motive := nextPrime.fixpoint_triple_motive) ?_ ?_ k
  · -- admissibility (boilerplate)
    apply admissible_pi_triple
    intro _
    -- TODO: we should be able to discharge this with vcgen maybe..
    simp [Named.mk]
  · -- assume it for the recursive call, prove it for the body
    intro p ih k
    velvet_vcgen [ih] with finish

/-! ## The same search as a loop

`while true` with a `break` once we find a prime. `done_with` says what holds when we
leave the loop, here through the `break`. -/

set_option velvet.semantics.termination "partial" in
method nextPrimeLoop (k : Nat) returns (res : Nat)
  ensures prime: isPrime res = true
  ensures ge: res ≥ k
do
  let mut i := k
  while true
    invariant i_ge: i ≥ k
    done_with found: isPrime i = true
  do
    if isPrime i then
      break
    i := i + 1
  return i

prove_correct nextPrimeLoop by
  velvet_vcgen [nextPrimeLoop] with finish

/-- info: some 97 -/
#guard_msgs in
#eval nextPrimeLoop 90

set_option velvet.verifyOnDefinition true in
method eqClause (n : Nat) returns (res : Nat)
  ensures wrong_eq: res = n + 1
do
  return n

end Tut02
