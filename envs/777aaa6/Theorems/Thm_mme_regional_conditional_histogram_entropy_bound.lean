-- Prove2me | Theorems.Thm_mme_regional_conditional_histogram_entropy_bound
-- name    : mme_regional_conditional_histogram_entropy_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T20:47:18.605836+00:00
-- url     : https://prove2.me/theorems/880746c3-b75b-468d-a898-128a3fb1a532
-- title:
--   Uniform conditional histogram lower bound from a joint profile
-- statement:
--   For an actual natural histogram whose word determines its coarse grade, derive an explicit lower bound using a nearby joint distribution, its uniform entropy modulus, the coarse histogram entropy, and a polynomial finite-size factor.
-- source:
--   Uniform regional entropy estimates for the actual integer CW construction in the More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . Supporting result; the numerical surplus certificate remains separate.

import Definitions.Def_mme_regional_split_entropy_data
import Mathlib
open BigOperators MME.RegionRate MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem mme_regional_conditional_histogram_entropy_bound {J W : Type*} [Fintype J] [Fintype W]
    (eta : J → W → ℕ) (n : ℕ) (hmass : ∑ j, ∑ w, eta j w = n)
    (hsparse : ∀ w j k, eta j w ≠ 0 → eta k w ≠ 0 → j = k)
    (p : W → ℝ) (hp : ∀ w, p w ∈ Set.Icc 0 1)
    (eps : ℝ) (heps : 0 ≤ eps)
    (htypical : ∀ w, |((∑ j, eta j w : ℕ) : ℝ) / n - p w| ≤ eps) :
    Real.exp ((n : ℝ) * entropy p - massEntropy (fun j ↦ ((∑ w, eta j w : ℕ) : ℝ)) -
      (n : ℝ) * entropyModulus W eps) ≤
      (6 * ((n : ℝ) + 1)) ^ (Fintype.card J * Fintype.card W) * histogramNumber eta := by sorry
