-- Prove2me | Theorems.Thm_mme_regional_entropy_uniform_modulus
-- name    : mme_regional_entropy_uniform_modulus
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T20:33:26.277972+00:00
-- url     : https://prove2.me/theorems/b2673919-1c2e-4f57-9776-415d08057c0a
-- title:
--   A uniform entropy modulus including zero probabilities
-- statement:
--   The explicitly defined supremum of entropy differences on a finite probability cube is finite, nonnegative, bounds every coordinatewise perturbation, and tends to zero with the tolerance. No lower bound on positive frequencies is assumed.
-- source:
--   Uniform regional entropy estimates for the actual integer CW construction in the More Asymmetry matrix multiplication campaign. Supporting result for https://arxiv.org/html/2404.16349v2#S6 . This result alone is not the regional extraction theorem or a numerical omega certificate.

import Definitions.Def_mme_regional_entropy_rate_data
import Definitions.Def_mme_recursive_thin_split_data
import Definitions.Def_mme_region_count_entropy_data
import Mathlib
open BigOperators MME.RegionRate MME.RegionRealization MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false

theorem mme_regional_entropy_uniform_modulus {W : Type*} [Fintype W] :
    (∀ eps : ℝ, 0 ≤ eps → 0 ≤ entropyModulus W eps) ∧
    (∀ (eps : ℝ) (p q : W → ℝ), (∀ w, p w ∈ Set.Icc 0 1) →
      (∀ w, q w ∈ Set.Icc 0 1) → (∀ w, |p w - q w| ≤ eps) →
      |entropy p - entropy q| ≤ entropyModulus W eps) ∧
    (∀ delta : ℝ, 0 < delta → ∃ eps : ℝ, 0 < eps ∧
      ∀ e : ℝ, 0 ≤ e → e ≤ eps → entropyModulus W e ≤ delta) := by sorry
