import Velvet

/-!
# Tutorial 5: Ghost State

Sometimes the proof needs to track something the program doesn't: how many steps it took,
what the state used to be, and so on. *Ghost* values exist for the proof but are erased
from the compiled code.

Here we use a ghost step counter to prove binary search takes at most `log₂ n + 1` steps.
-/

namespace Tut05

/-! ## A ghost step counter

We count steps in the state with a `Ghost Nat`, a counter that exists for the proof but
not at runtime. `tick` is one step of work. -/

abbrev Counted := StateT (Ghost Nat) Id

set_option velvet.verifyOnDefinition true in
method tick returns (_u : Unit) in Counted
  given (c₀ : Nat)
  requires (c : Ghost Nat) => c.reveal = c₀
  ensures (c : Ghost Nat) => c.reveal = c₀ + 1
do
  modify (·.modify (· + 1))

/-! ## Counting halvings

To talk about the cost, we need "how many times can we halve `w` before it hits 0", plus a
few facts about it for `grind` (see Tutorial 4). -/

def steps (w : Nat) : Nat := if w = 0 then 0 else steps (w / 2) + 1

theorem steps_zero : steps 0 = 0 := by simp [steps]

-- `@[grind =]` rewrites with this whenever `grind` sees `steps w`.
@[grind =] theorem steps_half {w : Nat} (h : w > 0) : steps w = steps (w / 2) + 1 := by
  rw [steps]; simp [Nat.ne_of_gt h]

theorem steps_mono {a b : Nat} (h : a ≤ b) : steps a ≤ steps b := by
  induction b using Nat.strongRecOn generalizing a with
  | _ b ih =>
    by_cases ha : a = 0
    · simp [ha, steps_zero]
    · rw [steps_half (by omega : a > 0), steps_half (by omega : b > 0)]
      have := ih (b / 2) (by omega) (Nat.div_le_div_right h)
      omega

theorem steps_le_log2 (n : Nat) : steps n ≤ n.log2 + 1 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h0 : n = 0
    · simp [h0, steps_zero]
    · rw [steps_half (by omega), Nat.log2_def]
      by_cases h2 : 2 ≤ n
      · simp only [h2, ite_true]
        have := ih (n / 2) (by omega)
        omega
      · have : n / 2 = 0 := by omega
        simp [this, steps_zero]

-- The other two need explicit patterns.
grind_pattern steps_mono => steps a, steps b
grind_pattern steps_le_log2 => steps n

/-! ## Binary search

The key invariant is `cost`: ticks so far, plus the halvings the window `hi - lo` still
has left, never exceed the halvings `a.size` had at the start.

(For stateful loops, `done_with` has to be written out.) -/

set_option velvet.verifyOnDefinition true in
method binarySearch (a : Array Int) (x : Int) returns (idx : Nat) in Counted
  given (c₀ : Nat)
  requires start: (c : Ghost Nat) => c.reveal = c₀
  requires sorted: (_ : Ghost Nat) => ∀ i j, i ≤ j → j < a.size → a[i]! ≤ a[j]!
  ensures in_range: (_ : Ghost Nat) => idx ≤ a.size
  ensures left: (_ : Ghost Nat) => ∀ j, j < idx → a[j]! < x
  ensures right: (_ : Ghost Nat) => ∀ j, idx ≤ j → j < a.size → x ≤ a[j]!
  ensures logarithmic: (c : Ghost Nat) => c.reveal ≤ c₀ + Nat.log2 a.size + 1
do
  let start ← get
  let mut lo := 0
  let mut hi := a.size
  while loop_cond: lo < hi
    invariant bounds: (fun _ : Ghost Nat => lo ≤ hi ∧ hi ≤ a.size)
    invariant below: (fun _ : Ghost Nat => ∀ j, j < lo → a[j]! < x)
    invariant above: (fun _ : Ghost Nat => ∀ j, hi ≤ j → j < a.size → x ≤ a[j]!)
    invariant cost: (fun c : Ghost Nat =>
      c.reveal + steps (hi - lo) ≤ start.reveal + steps a.size)
    decreasing by_width: hi - lo
    done_with found: (fun c : Ghost Nat =>
      lo = hi ∧ hi ≤ a.size ∧ (∀ j, j < lo → a[j]! < x) ∧
      (∀ j, hi ≤ j → j < a.size → x ≤ a[j]!) ∧
      c.reveal + steps (hi - lo) ≤ start.reveal + steps a.size)
  do
    tick
    let mid := (lo + hi) / 2
    if a[mid]! < x then
      lo := mid + 1
    else
      hi := mid
  return lo

/-! It runs like any other method, but there's no way to print the counter: `reveal`
isn't computable. The count exists only in the proof. -/

/-- info: 3 -/
#guard_msgs in
#eval ((binarySearch #[1, 3, 5, 7, 9, 11] 7).run (Ghost.mk 0)).1

end Tut05
