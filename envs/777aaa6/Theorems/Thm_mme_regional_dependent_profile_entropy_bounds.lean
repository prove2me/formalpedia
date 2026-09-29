-- Prove2me | Theorems.Thm_mme_regional_dependent_profile_entropy_bounds
-- name    : mme_regional_dependent_profile_entropy_bounds
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T20:47:27.643969+00:00
-- url     : https://prove2.me/theorems/3e9ba49e-f426-4a5a-8739-07e31d73eeb0
-- title:
--   Uniform entropy bounds across different parent alphabets
-- statement:
--   Bound the product of the actual multinomials for a region with varying parent split alphabets. Exponential rates are summed over the entire region, with an explicit polynomial loss in the total alphabet dimension.
-- source:
--   Uniform regional entropy estimates for the actual integer CW construction in the More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . Supporting result; the numerical surplus certificate remains separate.

import Definitions.Def_mme_regional_split_entropy_data
import Mathlib
open BigOperators MME.RegionRate MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem mme_regional_dependent_profile_entropy_bounds {R : Type*} [Fintype R] {A : R → Type*} [∀ r, Fintype (A r)]
    (mu : ∀ r, A r → ℕ) (S : ℕ) (hS : ∀ r, ∑ a, mu r a ≤ S) :
    (∏ r, ((∑ a, mu r a).factorial / ∏ a, (mu r a).factorial : ℕ) : ℝ) ≤
      Real.exp (∑ r, massEntropy (fun a ↦ (mu r a : ℝ))) ∧
    Real.exp (∑ r, massEntropy (fun a ↦ (mu r a : ℝ))) ≤
      (6 * ((S : ℝ) + 1)) ^ (∑ r, Fintype.card (A r)) *
        (∏ r, ((∑ a, mu r a).factorial / ∏ a, (mu r a).factorial : ℕ) : ℝ) := by sorry
