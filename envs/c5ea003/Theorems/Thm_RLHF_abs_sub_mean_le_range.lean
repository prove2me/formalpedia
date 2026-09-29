-- Prove2me | Theorems.Thm_RLHF_abs_sub_mean_le_range
-- name    : RLHF.abs_sub_mean_le_range
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:53:30.595549+00:00
-- url     : https://prove2.me/theorems/8c1645d3-4457-4163-a3a5-439cd480a8b2
-- title:
--   Every centred reward value is bounded by the reward range.
-- statement:
--   Every centred reward value is bounded by the reward range.
--
--   ```lean
--   theorem RLHF.abs_sub_mean_le_range{p r : Ω → ℝ} (hp : IsDist p) (y : Ω) :
--       |r y - mean p r| ≤ rewardRange r := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/RLHFDriftCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/RLHFDriftCore.lean#L150

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




/-! ## 2. Moment functionals -/









/-! ## 3. The Gibbs policy -/






variable [Nonempty Ω]

theorem RLHF.abs_sub_mean_le_range{p r : Ω → ℝ} (hp : IsDist p) (y : Ω) :
    |r y - mean p r| ≤ rewardRange r := by sorry
