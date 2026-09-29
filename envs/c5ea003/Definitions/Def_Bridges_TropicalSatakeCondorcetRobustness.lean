-- Prove2me | Definitions.Def_Bridges_TropicalSatakeCondorcetRobustness
-- name    : Bridges_TropicalSatakeCondorcetRobustness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:43:05.434068+00:00
-- url     : https://prove2.me/theorems/be89de90-ad5b-408a-b251-50a22144ba7e
-- title:
--   Aether Catalog definitions — Bridges_TropicalSatakeCondorcetRobustness
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalSatakeCondorcetRobustness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalSatakeCondorcetRobustness.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# GL₃ Tropical Satake Condorcet Robustness

This file formalizes a robust multiclass certification theorem for Condorcet-style
aggregation of pairwise tropical Satake score gaps. The central result is that
robustness of each pairwise gap lifts to robustness of the entire tournament winner
relation, provided one class has a strictly positive margin against every opponent.

## Main results

* `condorcet_winner_stable`: if class `c` beats every opponent by margin at least `m`
  and pairwise gaps shift by at most `δ < m`, then `c` remains a Condorcet winner.
* `unique_of_condorcet_winner`: a Condorcet winner is unique (by skew-symmetry of gaps).
* `condorcet_winner_of_pairwise_margin`: combines the above into a single theorem.
* `gl3_tropical_condorcet_certified`: specializes to the GL₃ tropical Satake setting
  with explicit perturbation bound `2 * K * d * ε`.
* `not_condorcetStable_of_small_margin`: sharpness — if one margin is at most `δ` and
  an adversary can flip that gap, the Condorcet winner is destroyed.

## Key definitions

* `PairwiseGap`: the score difference `s c x - s j x`.
* `CondorcetWinner`: class `c` beats every other class in pairwise comparison.
* `UniqueCondorcetWinner`: `c` is a Condorcet winner and no other class is.
-/

noncomputable section

open Finset

/-! ### Definitions -/

/-- The pairwise score gap between class `c` and class `j` at input `x`. -/
def PairwiseGap {C ι : Type*} [Fintype C] [DecidableEq C]
    (s : C → (ι → ℝ) → ℝ) (c j : C) (x : ι → ℝ) : ℝ :=
  s c x - s j x

/-- Class `c` is a Condorcet winner if it has strictly positive gap against every opponent. -/
def CondorcetWinner {C ι : Type*} [Fintype C] [DecidableEq C]
    (s : C → (ι → ℝ) → ℝ) (c : C) (x : ι → ℝ) : Prop :=
  ∀ j, j ≠ c → 0 < PairwiseGap s c j x

/-- Class `c` is the unique Condorcet winner. -/
def UniqueCondorcetWinner {C ι : Type*} [Fintype C] [DecidableEq C]
    (s : C → (ι → ℝ) → ℝ) (c : C) (x : ι → ℝ) : Prop :=
  CondorcetWinner s c x ∧ ∀ j, CondorcetWinner s j x → j = c

/-! ### Supporting lemmas -/



/-
If the absolute perturbation of a gap is at most `δ`, the perturbed gap is at least
the original gap minus `δ`.
-/

/-! ### Main theorems -/

/-
**Condorcet winner stability**: if `c` beats every opponent by margin ≥ `m` and pairwise
gaps shift by at most `δ < m`, then `c` remains a Condorcet winner at the perturbed input.
-/

/-
**Uniqueness of Condorcet winners**: if `c` is a Condorcet winner, then no other class
can also be a Condorcet winner. This follows from skew-symmetry of pairwise gaps.
-/

/-
**Full Condorcet robustness**: combining stability with uniqueness gives a unique
Condorcet winner at the perturbed input.
-/

/-
**Robust certificate with explicit radius**: if the minimum margin exceeds `2r` and
all pairwise gaps are Lipschitz with constant ≤ 1, then `c` is the unique Condorcet
winner in an `r`-ball around `x`.
-/

/-
**GL₃ tropical Satake Condorcet certified robustness**: specialization to the GL₃
tropical Satake setting with explicit perturbation bound `2 * K * d * ε`. The parameters
`K`, `d`, and `ε` represent the Lipschitz constant, dimension, and perturbation radius
from the tropical Satake score-gap robustness theorem.
-/

/-! ### Sharpness / Converse -/

/-
**Sharpness of margin threshold**: if some opponent `j` has margin at most `δ` from `c`
and the adversary achieves a nonpositive gap at `x'`, then `c` is not a Condorcet winner
at `x'`, hence not a unique Condorcet winner either.
-/

end


