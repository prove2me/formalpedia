-- Prove2me | solution 1 for UniversalRedundancy.disagreeProb_maxCoupling
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:25:02.378253+00:00
-- url     : https://prove2.me/submissions/084646b2-0f45-4c4a-9e3d-5787dff84d03

-- Sol generated from MachineLearning/TotalVariation/Coupling.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_Coupling
import Definitions.Def_MachineLearning_TotalVariation_EventSup
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Theorems.Thm_UniversalRedundancy_SourceClass_sum_min_eq_one_sub_tvDist
import Theorems.Thm_UniversalRedundancy_disagreeProb_eq_one_sub_diag
import Theorems.Thm_UniversalRedundancy_isCoupling_maxCoupling
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The coupling (Strassen) characterization of total variation

Third leg of the sharp-normalization thread.  `EventSup` characterized

`d_TV(p, q) = max_A (p(A) − q(A))`

as a supremum over *events*, and `Testing` cashed that in for hypothesis
testing.  This file proves the dual, *infimum*, characterization:

`d_TV(p, q) = min_{couplings c of (p, q)} ℙ_c[X ≠ Y]`.

Both directions are proved:

* every coupling has disagreement probability at least `d_TV`
  (`tvDist_le_disagreeProb`), by pushing the optimal *event* of `EventSup`
  through the coupling — so the two characterizations are genuinely dual;
* the explicit **maximal coupling**

  `c(x, y) = min(p x, q x)·[x = y] + (p x − min)₊ (q y − min)₊ / d_TV`

  attains it (`isCoupling_maxCoupling`, `disagreeProb_maxCoupling`).

The two together give `isLeast_disagreeProb`, and the sandwich
`max_A (p(A) − q(A)) = d_TV = min_c ℙ_c[X ≠ Y]` (`max_eventGap_eq_min_disagree`)
— a minimax identity whose two sides are witnessed by explicit optima.

The factor `1/2` is exactly what makes this work: with the `ℓ¹` normalization the
identity would read `min_c ℙ[X ≠ Y] = ‖p − q‖₁/2`, and the naive `ℓ¹` bound would
be off by two.

## Main results

* `IsCoupling`, `disagreeProb` — the coupling framework;
* `tvDist_le_disagreeProb` — the easy (but event-driven) direction;
* `isCoupling_maxCoupling`, `disagreeProb_maxCoupling` — the maximal coupling;
* `isLeast_disagreeProb`, `max_eventGap_eq_min_disagree` — the minimax identity;
* `eventGap_le_disagreeProb` — the coupling bound on distinguishing advantage.

## Application keywords

maximal coupling, Strassen's theorem, total variation, transport, minimax,
distinguishing advantage
-/


open Finset

open UniversalRedundancy

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Couplings -/




/-! ## Every coupling dominates the total variation distance -/



/-! ## The maximal coupling -/




omit [Fintype X] [DecidableEq X] in
lemma leftover_mul_eq_zero (p q : X → ℝ) (x : X) :
    (p x - min (p x) (q x)) * (q x - min (p x) (q x)) = 0 := by
  rcases le_total (p x) (q x) with h | h
  · rw [min_eq_left h]; ring
  · rw [min_eq_right h]; ring



/-- Pointwise unfolding of the maximal coupling. -/
lemma maxCoupling_apply (p q : X → ℝ) (x y : X) :
    maxCoupling p q x y = (if x = y then min (p x) (q x) else 0)
      + (if tvDist p q = 0 then 0
          else (p x - min (p x) (q x)) * (q y - min (p y) (q y)) / tvDist p q) := by
  simp only [maxCoupling]






open UniversalRedundancy in
theorem solution{p q : X → ℝ} (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) :
    disagreeProb (maxCoupling p q) = tvDist p q := by
  classical
  have hdiag : ∑ x, maxCoupling p q x x = 1 - tvDist p q := by
    have hpt : ∀ x : X, maxCoupling p q x x = min (p x) (q x) := by
      intro x
      rw [maxCoupling_apply]
      by_cases h : tvDist p q = 0
      · simp [h]
      · rw [if_pos rfl, if_neg h, leftover_mul_eq_zero p q x, zero_div, add_zero]
    rw [Finset.sum_congr rfl fun x _ => hpt x, SourceClass.sum_min_eq_one_sub_tvDist hp hq]
  rw [disagreeProb_eq_one_sub_diag (isCoupling_maxCoupling hp hq hp0 hq0) hp, hdiag]
  ring
