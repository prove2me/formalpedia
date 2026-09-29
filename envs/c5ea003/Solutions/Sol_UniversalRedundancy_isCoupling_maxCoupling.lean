-- Prove2me | solution 1 for UniversalRedundancy.isCoupling_maxCoupling
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:22:49.142765+00:00
-- url     : https://prove2.me/submissions/d684be90-032e-48d6-a664-f30dd45bda28

-- Sol generated from MachineLearning/TotalVariation/Coupling.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_Coupling
import Definitions.Def_MachineLearning_TotalVariation_EventSup
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Theorems.Thm_UniversalRedundancy_SourceClass_sum_min_eq_one_sub_tvDist
import Theorems.Thm_UniversalRedundancy_tvDist_eq_zero_iff
import Theorems.Thm_UniversalRedundancy_tvDist_nonneg
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


omit [DecidableEq X] in
lemma sum_posPart_left {p q : X → ℝ} (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) :
    ∑ x, (p x - min (p x) (q x)) = tvDist p q := by
  rw [Finset.sum_sub_distrib, hp, SourceClass.sum_min_eq_one_sub_tvDist hp hq]
  ring

omit [DecidableEq X] in
lemma sum_posPart_right {p q : X → ℝ} (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) :
    ∑ y, (q y - min (p y) (q y)) = tvDist p q := by
  rw [Finset.sum_sub_distrib, hq, SourceClass.sum_min_eq_one_sub_tvDist hp hq]
  ring


omit [Fintype X] [DecidableEq X] in
lemma leftover_left_nonneg (p q : X → ℝ) (x : X) : 0 ≤ p x - min (p x) (q x) := by
  have := min_le_left (p x) (q x); linarith

omit [Fintype X] [DecidableEq X] in
lemma leftover_right_nonneg (p q : X → ℝ) (y : X) : 0 ≤ q y - min (p y) (q y) := by
  have := min_le_right (p y) (q y); linarith

/-- Pointwise unfolding of the maximal coupling. -/
lemma maxCoupling_apply (p q : X → ℝ) (x y : X) :
    maxCoupling p q x y = (if x = y then min (p x) (q x) else 0)
      + (if tvDist p q = 0 then 0
          else (p x - min (p x) (q x)) * (q y - min (p y) (q y)) / tvDist p q) := by
  simp only [maxCoupling]






open UniversalRedundancy in
theorem solution{p q : X → ℝ} (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) :
    IsCoupling p q (maxCoupling p q) := by
  classical
  have hzero : tvDist p q = 0 → p = q := fun h => (tvDist_eq_zero_iff p q).mp h
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    rw [maxCoupling_apply]
    have h1 : (0:ℝ) ≤ if x = y then min (p x) (q x) else 0 := by
      by_cases h : x = y
      · rw [if_pos h]; exact le_min (hp0 x) (hq0 x)
      · simp [h]
    have h2 : (0:ℝ) ≤ if tvDist p q = 0 then 0
        else (p x - min (p x) (q x)) * (q y - min (p y) (q y)) / tvDist p q := by
      by_cases h : tvDist p q = 0
      · simp [h]
      · rw [if_neg h]
        have hpos : 0 < tvDist p q := lt_of_le_of_ne (tvDist_nonneg p q) (Ne.symm h)
        exact div_nonneg (mul_nonneg (leftover_left_nonneg p q x)
          (leftover_right_nonneg p q y)) hpos.le
    exact add_nonneg h1 h2
  · intro x
    rw [Finset.sum_congr rfl fun y (_ : y ∈ univ) => maxCoupling_apply p q x y,
      Finset.sum_add_distrib, Finset.sum_ite_eq]
    by_cases h : tvDist p q = 0
    · have hpq := hzero h
      subst hpq
      simp
    · rw [Finset.sum_congr rfl fun y (_ : y ∈ univ) => if_neg h]
      have hfac : ∑ y, (p x - min (p x) (q x)) * (q y - min (p y) (q y)) / tvDist p q
          = (p x - min (p x) (q x)) * (∑ y, (q y - min (p y) (q y))) / tvDist p q := by
        rw [Finset.mul_sum, Finset.sum_div]
      rw [hfac, sum_posPart_right hp hq, mul_div_assoc, div_self h, mul_one,
        if_pos (Finset.mem_univ x)]
      ring
  · intro y
    have hcol : ∀ x : X, maxCoupling p q x y
        = (if x = y then min (p y) (q y) else 0)
          + (if tvDist p q = 0 then 0
              else (p x - min (p x) (q x)) * (q y - min (p y) (q y)) / tvDist p q) := by
      intro x
      rw [maxCoupling_apply]
      by_cases h : x = y
      · subst h; simp
      · simp [h]
    rw [Finset.sum_congr rfl fun x (_ : x ∈ univ) => hcol x, Finset.sum_add_distrib]
    have hdiag : ∑ x, (if x = y then min (p y) (q y) else 0) = min (p y) (q y) := by
      simp
    rw [hdiag]
    by_cases h : tvDist p q = 0
    · have hpq := hzero h
      subst hpq
      simp
    · rw [Finset.sum_congr rfl fun x (_ : x ∈ univ) => if_neg h]
      have hfac : ∑ x, (p x - min (p x) (q x)) * (q y - min (p y) (q y)) / tvDist p q
          = (∑ x, (p x - min (p x) (q x))) * (q y - min (p y) (q y)) / tvDist p q := by
        rw [Finset.sum_mul, Finset.sum_div]
      rw [hfac, sum_posPart_left hp hq, mul_comm, mul_div_assoc, div_self h, mul_one]
      ring
