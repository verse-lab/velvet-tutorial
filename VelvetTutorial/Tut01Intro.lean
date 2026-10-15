import Velvet
import Plausible

/-!
# Tutorial 1: Introduction to Velvet

Velvet lets you write imperative programs in Lean, give them Dafny-style contracts, and
prove those contracts, mostly automatically. Since it's all Lean, the same program can
also be run and tested.

We start in the default mode, *total correctness*: verified programs must also terminate.
-/

namespace Tut01

method absDiff (x y : Int) returns (res : Int)
  ensures nonneg: res ≥ 0
  ensures dist: res = x - y ∨ res = y - x
do
  if x ≥ y then
    return x - y
  else
    return y - x

/-! A method is just a Lean function. By default it lives in `Option`. -/
#check absDiff

/-- info: some 7 -/
#guard_msgs in
#eval absDiff 3 10

/-! Now let's prove it. `velvet_vcgen` generates the verification conditions and `finish`
closes them. -/

prove_correct absDiff by
  velvet_vcgen [absDiff] with finish

/-! That gives us a theorem, `absDiff.spec`. -/
#check absDiff.spec

/-! ## Verifying on definition

If `finish` does all the work anyway, we can skip `prove_correct` and verify each method
as soon as it's defined. -/

set_option velvet.verifyOnDefinition true

/-! ## `while` loops

Loops need an `invariant` and, in total mode, a `decreasing` measure. -/

method divMod (n d : Nat) returns (res : Nat × Nat)
  requires d_pos: d > 0
  ensures sum_ok: res.1 * d + res.2 = n
  ensures rem_lt: res.2 < d
do
  let mut q := 0
  let mut r := n
  while loop_cond: r ≥ d
    invariant inv: q * d + r = n
    decreasing by_r: r
  do
    q := q + 1
    r := r - d
  return (q, r)

/-- info: some (3, 2) -/
#guard_msgs in
#eval divMod 17 5

/-! Already verified. Try changing `r ≥ d` to `r > d` and see what happens. -/
#check divMod.spec

/-! ## `for` loops

No measure needed here. `__pref` is the part of the list we've already seen. Because it
goes out of scope after the loop, we say what holds at the end with `done_with`. -/

method sumList (xs : List Nat) returns (s : Nat)
  ensures s = xs.sum
do
  let mut acc := 0
  for x in xs
    invariant acc_pref: acc = __pref.sum
    done_with acc_done: acc = xs.sum
  do
    acc := acc + x
  return acc

/-- info: some 10 -/
#guard_msgs in
#eval sumList [1, 2, 3, 4]

-- Ranges work too.
method sumDoubles (n : Nat) returns (res : Nat)
  requires True
  ensures even: res % 2 = 0
do
  let mut acc := 0
  for i in 0...n
    invariant acc_even: acc % 2 = 0
  do
    acc := acc + 2 * i
  return acc

/-! ## Arrays

Find the first index holding `x`, or `a.size` if there isn't one. -/

method linearSearch (a : Array Int) (x : Int) returns (idx : Nat)
  ensures bound: idx ≤ a.size
  ensures hit: idx < a.size → a[idx]! = x
  ensures first: ∀ j, j < idx → a[j]! ≠ x
do
  let mut i := 0
  while loop_cond: i < a.size ∧ a[i]! ≠ x
    invariant i_le: i ≤ a.size
    invariant not_yet: ∀ j, j < i → a[j]! ≠ x
    decreasing by_rem: a.size - i
  do
    i := i + 1
  return i

/-- info: some 2 -/
#guard_msgs in
#eval linearSearch #[5, 7, 9, 7] 9

/-! ## Calling other methods

When `max3` calls `max2`, Velvet only uses `max2`'s contract, not its code.
`assert` checks a fact in the middle of a method. -/

method max2 (x y : Int) returns (res : Int)
  ensures ge: res ≥ x ∧ res ≥ y
  ensures one_of: res = x ∨ res = y
do
  if x ≥ y then return x else return y

method max3 (x y z : Int) returns (res : Int)
  ensures ge: res ≥ x ∧ res ≥ y ∧ res ≥ z
  ensures one_of: res = x ∨ res = y ∨ res = z
do
  let m ← max2 x y
  assert m_ok: m ≥ x ∧ m ≥ y
  let r ← max2 m z
  return r

/-! ## Absence and presence of bugs

A proof shows there are no bugs. A test can show there is one, and it's much cheaper to
run. Here's `divMod` with a bug: `r > d` instead of `r ≥ d`. -/

set_option velvet.verifyOnDefinition false

method divModBuggy (n d : Nat) returns (res : Nat × Nat)
  requires d_pos: d > 0
  ensures spec: res.1 * d + res.2 = n ∧ res.2 < d
do
  let mut q := 0
  let mut r := n
  while loop_cond: r > d
    invariant inv: q * d + r = n
    decreasing by_r: r
  do
    q := q + 1
    r := r - d
  return (q, r)

/-! Velvet can turn the contract into a checker. It answers `pass`, `fail`, or `discard`
(when the precondition doesn't hold).

(In this version the tester wants a single `ensures`, hence the `∧` above.) -/

open Velvet.Testing

#derive_tester_for divModBuggy

/-- info: Velvet.Testing.TestVerdict.pass -/
#guard_msgs in
#eval divModBuggy.check 7 2

/-- info: Velvet.Testing.TestVerdict.fail -/
#guard_msgs in
#eval divModBuggy.check 6 3

/-- info: Velvet.Testing.TestVerdict.discard -/
#guard_msgs in
#eval divModBuggy.check 6 0

/-! Or throw random inputs at it with Plausible: -/

run_elab do
  let mut counterexample : Option (Nat × Nat) := none
  for _ in [0:100] do
    let (n, d) ← Plausible.Gen.run (do
      let n ← Plausible.SampleableExt.interpSample Nat
      let d ← Plausible.SampleableExt.interpSample Nat
      return (n, d)) 20
    if counterexample.isNone && divModBuggy.check n d == .fail then
      counterexample := some (n, d)
  match counterexample with
  | some (n, d) => Lean.logInfo m!"counterexample: n = {n}, d = {d}"
  | none => Lean.logInfo "no counterexample found in 100 tests"

-- Once we've found the bug, Lean can confirm it:
example : divModBuggy 6 3 = some (1, 3) := by native_decide

/-! And if we try to verify it, the error lands right on `ensures rem_lt`. -/

set_option velvet.verifyOnDefinition true in
method divModBuggy' (n d : Nat) returns (res : Nat × Nat)
  requires d_pos: d > 0
  ensures sum_ok: res.1 * d + res.2 = n
  ensures rem_lt: res.2 < d
do
  let mut q := 0
  let mut r := n
  while loop_cond: r > d
    invariant inv: q * d + r = n
    decreasing by_r: r
  do
    q := q + 1
    r := r - d
  return (q, r)

end Tut01
