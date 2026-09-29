-- Prove2me | solution 1 for Algebra.RLHF.IsPosDist.isDist
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T00:54:05.050766+00:00
-- url     : https://prove2.me/submissions/fb79e784-23f2-46cc-890e-9bead435cea2

-- Thm stub generated from Algebra/RLHFDriftCore.lean
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

theorem solution{p : Ω → ℝ} (hp : IsPosDist p) : IsDist p := ⟨fun y => (hp.pos y).le, hp.total⟩
