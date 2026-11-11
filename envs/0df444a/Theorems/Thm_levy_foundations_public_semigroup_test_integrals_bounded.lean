-- Prove2me | Theorems.Thm_levy_foundations_public_semigroup_test_integrals_bounded
-- name    : levy_foundations_public_semigroup_test_integrals_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:11:59.680697+00:00
-- url     : https://prove2.me/theorems/b4b24338-55c0-4926-ac9a-a0eb9dae04a1
-- title:
--   M5 uniform scaled test-integral bound away from zero
-- statement:
--   Every bounded continuous real test function vanishing on a neighbourhood of zero has uniformly bounded scaled integrals against the positive-time convolution semigroup measures. This follows from the proven uniform bound on scaled mass outside any positive radius and supplies the bounded functional family used in the diagonal vague-compactness step of Lévy-measure extraction.
-- source:
--   Source-faithful analytic bound implied by existing public Proved scaled-largeSet-mass bound ba89e103-e067-4ec7-8ada-89d6391b6da1; prerequisite for vague sequential extraction a407ec20-f0b2-46a7-a269-5aaad3eb2279 and M5 representation 565f0003-bc9c-4123-b378-30ee3aa5c747.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_semigroup_scaled_largeSet_mass_bound
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_semigroup_test_integrals_bounded
    (S : ProbabilityTheory.ConvolutionSemigroup)
    (f : BoundedContinuousFunction ℝ ℝ)
    (hf : ∃ r : ℝ, 0 < r ∧ ∀ x, |x| < r → f x = 0) :
    ∃ C : ℝ, ∀ t : {t : ℝ // 0 < t},
      |t.val⁻¹ * ∫ x, f x ∂(S.measure t : Measure ℝ)| ≤ C := by sorry
