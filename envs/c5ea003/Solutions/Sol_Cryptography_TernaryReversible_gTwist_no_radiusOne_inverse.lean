-- Prove2me | solution 1 for Cryptography.TernaryReversible.gTwist_no_radiusOne_inverse
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:05:50.368979+00:00
-- url     : https://prove2.me/submissions/6fe4028d-cdeb-4e82-874e-b02983d52a5c

-- Sol generated from Cryptography/TernaryReversible/InverseRadius.lean
import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_Core
import Definitions.Def_Cryptography_TernaryReversible_InverseRadius

/-!
# A reversible ternary radius-one rule whose inverse is not radius one

The refutation in `Cryptography.TernaryReversible.Refutation` produces rules that are
bijective on every cycle but still decode with a *radius-one* inverse (they are
involutions).  This file goes one step further and exhibits a rule for which local
reversibility is genuinely non-local: the **conditional-transposition rule**

`gTwist a b c = if (b ≠ 0 ∧ c = 2) then swap01 a else a`,

which copies the left neighbour, transposing the values `0` and `1` exactly when the
pattern `(b ≠ 0, c = 2)` occurs to its right.

## Main results

* `gTwist_decoder4` / `gTwist_cycleBijective`: `gTwist` is bijective on every nonempty
  finite cycle, because a window-*four* decoder reconstructs each cell from the four
  output cells to its right.
* `gTwist_no_window3_decoder`: **no** window-three decoder exists, at *any* of the five
  possible offsets; so the inverse automaton has neighbourhood width at least four.
* `gTwist_no_radiusOne_inverse`: in particular `gTwist` has no radius-one inverse
  cellular automaton.
* `gTwist_deps`: `gTwist` also uses two cells of its window, hence is one more
  counterexample to the classification claim, of a shape different from the
  sign-twisted involutions.

The mechanism: the transposition `swap01` fixes the letter `2`, so the positions
carrying `2` are visible in the output, but deciding whether the *condition* fired at a
cell requires knowing whether its right neighbour is nonzero, which in turn requires
looking one cell further right.  The information needed to invert therefore travels a
bounded but strictly larger distance than the rule itself.
-/

open Cryptography
open TernaryReversible






/-! ## The inverse is not radius one -/









/-! ## `gTwist` is a counterexample of a new shape -/







open Cryptography.TernaryReversible in
theorem solution:
    ¬ ∃ d : LocalRule, ∀ (n : ℕ) (s : ZMod n → Alph),
        globalMap d (globalMap gTwist s) = s := by
  rintro ⟨d, hd⟩
  have h1 := congrFun (hd 5 (fun _ => 0)) 2
  have h2 := congrFun (hd 5 conf5) 2
  have e1 : globalMap gTwist conf5 (2 - 1) = globalMap gTwist (fun _ : ZMod 5 => 0) (2 - 1) := by
    decide
  have e2 : globalMap gTwist conf5 2 = globalMap gTwist (fun _ : ZMod 5 => 0) 2 := by
    decide
  have e3 : globalMap gTwist conf5 (2 + 1) = globalMap gTwist (fun _ : ZMod 5 => 0) (2 + 1) := by
    decide
  have key : globalMap d (globalMap gTwist conf5) 2
      = globalMap d (globalMap gTwist (fun _ : ZMod 5 => 0)) 2 := by
    show d (globalMap gTwist conf5 (2 - 1)) (globalMap gTwist conf5 2)
        (globalMap gTwist conf5 (2 + 1))
      = d (globalMap gTwist (fun _ : ZMod 5 => 0) (2 - 1))
        (globalMap gTwist (fun _ : ZMod 5 => 0) 2)
        (globalMap gTwist (fun _ : ZMod 5 => 0) (2 + 1))
    rw [e1, e2, e3]
  rw [h1, h2] at key
  exact absurd key (by decide)
