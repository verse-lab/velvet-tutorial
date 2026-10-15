import Velvet

/-!
# Tutorial 3: Stateful Programs and Non-deterministic Choice

With `in <Monad>` a method can use state, exceptions, or non-deterministic choice, and
its contract can talk about them.
-/

namespace Tut03

set_option velvet.verifyOnDefinition true

/-! ## Stateful programs

A bank account. `(b : Nat) =>` binds the balance, before the call in `requires` and
after it in `ensures`. `given (b₀ : Nat)` names the starting balance so `ensures` can
refer to it. -/

method deposit (amt : Nat) returns (res : Nat) in StateM Nat
  given (b₀ : Nat)
  requires (b : Nat) => b = b₀
  ensures (b : Nat) => b = b₀ + amt ∧ res = b
do
  modify (· + amt)
  get

#check @deposit.spec

-- Run it from a starting balance of 10.
/-- info: (15, 15) -/
#guard_msgs in
#eval (deposit 5).run 10

/-! ## Exceptions

`signals` says when a method may throw, and what it throws. -/

method withdraw (amt : Nat) returns (res : Nat) in StateT Nat (Except String)
  given (b₀ : Nat)
  requires (b : Nat) => b = b₀
  signals insufficient: (e : String) => e = "insufficient funds" ∧ amt > b₀
  ensures (b : Nat) => b + amt = b₀ ∧ res = b
do
  let b ← get
  if amt > b then
    throw "insufficient funds"
  set (b - amt)
  return (b - amt)

/-- info: Except.ok (5, 5) -/
#guard_msgs in
#eval (withdraw 5).run 10

/-- info: Except.error "insufficient funds" -/
#guard_msgs in
#eval (withdraw 50).run 10

/-! ## Putting them together

The loop invariant is now a predicate on the balance. `given` variables can't appear in
the body, so we read the starting balance into `start`. -/

method payAll (bills : List Nat) returns (paid : Nat) in StateT Nat (Except String)
  given (b₀ : Nat)
  requires (b : Nat) => b = b₀
  signals (e : String) => e = "insufficient funds"
  ensures (b : Nat) => b + paid = b₀ ∧ paid = bills.sum
do
  let start ← get
  for x in bills
    invariant paid_so_far: (fun b : Nat => b + __pref.sum = start)
    done_with all_paid: (fun b : Nat => b + bills.sum = start)
  do
    let _ ← withdraw x
  return bills.sum

/-- info: Except.ok (6, 4) -/
#guard_msgs in
#eval (payAll [1, 2, 3]).run 10

/-- info: Except.error "insufficient funds" -/
#guard_msgs in
#eval (payAll [1, 20, 3]).run 10

/-! ## Testing stateful methods

The checker's arguments are the method arguments, then the `given` variables, then the
initial state. -/

open Velvet.Testing

#derive_tester_for withdraw

/-- info: Velvet.Testing.TestVerdict.pass -/
#guard_msgs in
#eval withdraw.check 5 10 10

/-- info: Velvet.Testing.TestVerdict.pass -/
#guard_msgs in
#eval withdraw.check 50 10 10  -- throws, which `signals` allows

/-- info: Velvet.Testing.TestVerdict.discard -/
#guard_msgs in
#eval withdraw.check 5 10 7    -- precondition fails

/-! ## Demonic choice

`let x :| P x` picks some `x` satisfying `P`. In `DemonicT` the contract must hold for
*every* such `x`. We still have to show that some `x` exists, and that's the one goal we
prove by hand. -/

set_option velvet.verifyOnDefinition false

method pickEven (n : Nat) returns (res : Nat) in DemonicT Option
  signals False
  ensures even: res % 2 = 0
  ensures ge: res ≥ n
do
  let (x : Nat) :| x % 2 = 0 ∧ x ≥ n
  return x

prove_correct pickEven by
  velvet_vcgen [pickEven] with try finish
  case signals1 =>
    rename_i n no_choice
    exact no_choice ⟨2 * n, by omega, by omega⟩

-- It still runs: `.run` searches for a value.
/-- info: some 8 -/
#guard_msgs in
#eval (pickEven 7).run

/-! ## Angelic choice

In `AngelicT` the contract only has to hold for *some* choice, so the proof has to pick
one. A divisor of 91? Let's go with 7. -/

method findDivisor (n : Nat) returns (d : Nat) in AngelicT Option
  requires is91: n = 91
  signals False
  ensures d > 1 ∧ d < n ∧ n % d = 0
do
  let (c : Nat) :| c > 1 ∧ c < n ∧ n % c = 0
  return c

prove_correct findDivisor by
  velvet_vcgen [findDivisor] with try finish
  case vc3 => exact 7
  all_goals (subst_vars; decide)

/-- info: some 7 -/
#guard_msgs in
#eval (findDivisor 91).run

end Tut03
