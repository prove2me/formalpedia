-- Prove2me | Theorems.Thm_mme_regional_same_marginal_integer_entropy_bound
-- name    : mme_regional_same_marginal_integer_entropy_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T20:47:35.609101+00:00
-- url     : https://prove2.me/theorems/aceef6a3-3d02-4acd-9126-2613c39bf24f
-- title:
--   Entropy control for integer competitors with the same marginals
-- statement:
--   Translate the existing real maximum-entropy penalty into a finite mass-entropy bound for every integer joint profile with the prescribed physical marginals, including mass zero.
-- source:
--   Uniform regional entropy estimates for the actual integer CW construction in the More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . Supporting result; the numerical surplus certificate remains separate.

import Definitions.Def_mme_regional_split_entropy_data
import Mathlib
open BigOperators MME.RegionRate MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem mme_regional_same_marginal_integer_entropy_bound {half : ℕ} {parent : Fin 3 → ℕ} (m v : Split half parent → ℕ) (n : ℕ)
    (hm : ∑ c, m c = n) (hv : ∑ c, v c = n)
    (hmargin : ∀ i j, (∑ c : {c : Split half parent // c.val i = j}, v c.val) =
      ∑ c : {c : Split half parent // c.val i = j}, m c.val) :
    0 ≤ (n : ℝ) * Real.log 2 * entropyPenalty (fun c ↦ (m c : ℝ) / n) ∧
    massEntropy (fun c ↦ (v c : ℝ)) ≤ massEntropy (fun c ↦ (m c : ℝ)) +
      (n : ℝ) * Real.log 2 * entropyPenalty (fun c ↦ (m c : ℝ) / n) := by sorry
