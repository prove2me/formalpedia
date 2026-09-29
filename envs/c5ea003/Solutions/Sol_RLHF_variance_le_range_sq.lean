-- Prove2me | solution 1 for RLHF.variance_le_range_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:06:21.1724+00:00
-- url     : https://prove2.me/submissions/42d47ef6-a19e-4fd3-b926-6f8e03fc3909

-- Sol generated from Algebra/RLHFDriftCore.lean
import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
import Theorems.Thm_RLHF_sum_centered

/-!
# Core objects of the RLHF alignment-drift catalogue

Domain: Algebra (convex analysis × information theory × alignment theory).

This file collects the base objects that the RLHF drift thread of the catalogue is
phrased in — finite probability vectors, the Gibbs (KL-regularised) policy, the
Kullback–Leibler divergence, the total-variation (`ℓ¹`) distance, and the first two
moment functionals of a reward — together with the elementary API used downstream.

The names and definitions follow the conventions of the RLHF drift files of the
catalogue (`RLHF.IsDist`, `RLHF.gibbsPolicy`, `RLHF.klDiv`, `RLHF.l1Dist`,
`RLHF.rewardRange`, `RLHF.mean`, `RLHF.variance`, ...), so the results proved here and
in `Algebra.RLHFMeanAbsoluteDeviation` / `Algebra.RLHFKLSecondOrder` speak about
exactly the same objects as `RLHF.kl_gibbs_le_variance` and
`RLHF.gibbs_l1_le_variance`.

Nothing in this file is deep; it exists so that the two research files that follow are
self-contained and compile.
-/

open RLHF

open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## 1. Finite probability vectors -/




/-! ## 2. Moment functionals -/









/-! ## 3. The Gibbs policy -/






variable [Nonempty Ω]






omit [Nonempty Ω] in
/-- The mean minimises the mean square deviation: `Var_p(f) ≤ 𝔼_p[(f − c)²]` for every
centre `c`. -/
theorem variance_le_of_center {p : Ω → ℝ} (hp : IsDist p) (f : Ω → ℝ) (c : ℝ) :
    variance p f ≤ ∑ y, p y * (f y - c) ^ 2 := by
  have hexpand : ∀ y, p y * (f y - c) ^ 2
      = p y * (f y - mean p f) ^ 2 + 2 * (mean p f - c) * (p y * (f y - mean p f))
        + (mean p f - c) ^ 2 * p y := fun y => by ring
  rw [Finset.sum_congr rfl fun y _ => hexpand y, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_centered hp f, hp.total]
  have hsq : (0:ℝ) ≤ (mean p f - c) ^ 2 := sq_nonneg _
  simp only [variance, mul_zero, mul_one, add_zero]
  linarith




open RLHF in
theorem solution{p r : Ω → ℝ} (hp : IsDist p) :
    variance p r ≤ rewardRange r ^ 2 / 4 := by
  set c : ℝ := (univ.sup' univ_nonempty r + univ.inf' univ_nonempty r) / 2 with hc
  refine (variance_le_of_center hp r c).trans ?_
  have hpt : ∀ y ∈ (univ : Finset Ω), p y * (r y - c) ^ 2 ≤ p y * (rewardRange r ^ 2 / 4) := by
    intro y _
    refine mul_le_mul_of_nonneg_left ?_ (hp.nonneg y)
    have h1 : r y ≤ univ.sup' univ_nonempty r := Finset.le_sup' r (mem_univ y)
    have h2 : univ.inf' univ_nonempty r ≤ r y := Finset.inf'_le r (mem_univ y)
    simp only [rewardRange, hc]
    nlinarith [sq_nonneg (r y - c)]
  have hsum := Finset.sum_le_sum hpt
  rwa [← Finset.sum_mul, hp.total, one_mul] at hsum
