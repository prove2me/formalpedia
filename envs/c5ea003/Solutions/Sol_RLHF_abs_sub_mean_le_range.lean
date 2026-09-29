-- Prove2me | solution 1 for RLHF.abs_sub_mean_le_range
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:58:59.948724+00:00
-- url     : https://prove2.me/submissions/3d29dbeb-5acc-4112-8333-5758d669918f

-- Sol generated from Algebra/RLHFDriftCore.lean
import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore

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



theorem mean_le_sup {p r : Ω → ℝ} (hp : IsDist p) : mean p r ≤ univ.sup' univ_nonempty r := by
  have h : ∀ y ∈ (univ : Finset Ω), p y * r y ≤ p y * univ.sup' univ_nonempty r :=
    fun y _ => mul_le_mul_of_nonneg_left (Finset.le_sup' r (mem_univ y)) (hp.nonneg y)
  have := Finset.sum_le_sum h
  rwa [← Finset.sum_mul, hp.total, one_mul] at this

theorem inf_le_mean {p r : Ω → ℝ} (hp : IsDist p) : univ.inf' univ_nonempty r ≤ mean p r := by
  have h : ∀ y ∈ (univ : Finset Ω), p y * univ.inf' univ_nonempty r ≤ p y * r y :=
    fun y _ => mul_le_mul_of_nonneg_left (Finset.inf'_le r (mem_univ y)) (hp.nonneg y)
  have := Finset.sum_le_sum h
  rwa [← Finset.sum_mul, hp.total, one_mul] at this






open RLHF in
theorem solution{p r : Ω → ℝ} (hp : IsDist p) (y : Ω) :
    |r y - mean p r| ≤ rewardRange r := by
  have h1 : r y ≤ univ.sup' univ_nonempty r := Finset.le_sup' r (mem_univ y)
  have h2 : univ.inf' univ_nonempty r ≤ r y := Finset.inf'_le r (mem_univ y)
  have h3 := mean_le_sup (p := p) (r := r) hp
  have h4 := inf_le_mean (p := p) (r := r) hp
  rw [abs_le]
  simp only [rewardRange]
  constructor <;> linarith
