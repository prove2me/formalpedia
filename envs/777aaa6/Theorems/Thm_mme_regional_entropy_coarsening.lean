-- Prove2me | Theorems.Thm_mme_regional_entropy_coarsening
-- name    : mme_regional_entropy_coarsening
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T20:48:19.695775+00:00
-- url     : https://prove2.me/theorems/e8511a95-5c7e-4c35-b0e2-dab4d3949b34
-- title:
--   Coarsening cannot increase finite mass entropy
-- statement:
--   Prove that the mass entropy of a grouped nonnegative vector is at most its original mass entropy, by exact fiber decomposition and nonnegative conditional entropy.
-- source:
--   Uniform regional entropy estimates for the actual integer CW construction in the More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . Supporting result; the numerical surplus certificate remains separate.

import Definitions.Def_mme_regional_split_entropy_data
import Mathlib
open BigOperators MME.RegionRate
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem mme_regional_entropy_coarsening {A J : Type*} [Fintype A] [Fintype J] (g : A → J)
    (x : A → ℝ) (hx : ∀ a, 0 ≤ x a) :
    massEntropy (fun j ↦ ∑ a : {a // g a = j}, x a.val) ≤ massEntropy x := by sorry
