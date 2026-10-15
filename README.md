# VelvetTutorial

A short tutorial for [Velvet](https://github.com/verse-lab/velvet), a Dafny-style verifier
for imperative programs embedded in Lean.

Open the chapters in VS Code and read them in order. Each one is a Lean file you can step
through, with explanations in comments.

| Chapter | Covers |
| :--- | :--- |
| [Tut01Intro](VelvetTutorial/Tut01Intro.lean) | Methods and contracts, `prove_correct`, `verifyOnDefinition`, `while`/`for` loops, arrays, `assert`, method calls, finding bugs by testing vs. proving their absence |
| [Tut02Termination](VelvetTutorial/Tut02Termination.lean) | Total vs. partial correctness, loops without a termination measure, `break`, recursion by induction and by fixpoint induction |
| [Tut03EffectsAndNonDet](VelvetTutorial/Tut03EffectsAndNonDet.lean) | Stateful programs (`StateT`), exceptions (`signals`), composing stateful methods, demonic and angelic choice |
| [Tut04InteractiveProofs](VelvetTutorial/Tut04InteractiveProofs.lean) | When `finish` fails: the VC report, `with try finish` and `case <label>`, teaching `grind` a lemma with `grind_pattern` |
| [Tut05GhostState](VelvetTutorial/Tut05GhostState.lean) | Ghost state: a `StateT (Ghost Nat)` step counter proving binary search takes at most `log₂ n + 1` steps |

## Building

```bash
lake build
```

The tutorial pins Velvet at tag `v2.0` (Lean `v4.34.0`).
