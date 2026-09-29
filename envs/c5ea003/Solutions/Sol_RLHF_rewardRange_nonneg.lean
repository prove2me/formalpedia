-- Prove2me | solution 1 for RLHF.rewardRange_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:06:20.099723+00:00
-- url     : https://prove2.me/submissions/d7c85619-613b-42d1-b323-fd90ab126275

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










open RLHF in
theorem solution(r : Ω → ℝ) : 0 ≤ rewardRange r := by
  obtain ⟨y⟩ := ‹Nonempty Ω›
  have h1 : r y ≤ univ.sup' univ_nonempty r := Finset.le_sup' r (mem_univ y)
  have h2 : univ.inf' univ_nonempty r ≤ r y := Finset.inf'_le r (mem_univ y)
  simp only [rewardRange]; linarith
