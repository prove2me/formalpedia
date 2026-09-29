-- Prove2me | solution 1 for UniversalRedundancy.eventGap_le_disagreeProb
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:25:03.588516+00:00
-- url     : https://prove2.me/submissions/e5c618e7-6f50-4892-9f9c-a0bb1e1dafb6

-- Sol generated from MachineLearning/TotalVariation/Coupling.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_Coupling
import Definitions.Def_MachineLearning_TotalVariation_EventSup
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













open UniversalRedundancy in
theorem solution{p q : X → ℝ} {c : X → X → ℝ} (hc : IsCoupling p q c)
    (A : Finset X) : eventGap p q A ≤ disagreeProb c := by
  classical
  have hind : ∀ r : X → ℝ, ∀ B : Finset X, ∑ x ∈ B, r x
      = ∑ x, r x * (if x ∈ B then (1:ℝ) else 0) := by
    intro r B
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
  have hleft : eventProb p A = ∑ x, ∑ y, c x y * (if x ∈ A then (1:ℝ) else 0) := by
    rw [eventProb, hind p A]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← hc.left x, Finset.sum_mul]
  have hright : eventProb q A = ∑ x, ∑ y, c x y * (if y ∈ A then (1:ℝ) else 0) := by
    rw [eventProb, hind q A, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← hc.right y, Finset.sum_mul]
  have hdiff : eventGap p q A
      = ∑ x, ∑ y, c x y * ((if x ∈ A then (1:ℝ) else 0) - (if y ∈ A then (1:ℝ) else 0)) := by
    rw [eventGap, hleft, hright, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hdiff, disagreeProb]
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [if_neg hxy]
    have hle : (if x ∈ A then (1:ℝ) else 0) - (if y ∈ A then (1:ℝ) else 0) ≤ 1 := by
      by_cases h1 : x ∈ A <;> by_cases h2 : y ∈ A <;> simp [h1, h2]
    nlinarith [hc.nonneg x y]
