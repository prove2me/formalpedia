-- Prove2me | Theorems.Thm_levy_foundations_public_gaussian_band_exhaustion
-- name    : levy_foundations_public_gaussian_band_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T10:29:27.073192+00:00
-- url     : https://prove2.me/theorems/54de6b4a-537c-4e9d-8908-c116d3d35fd2
-- title:
--   Exhaust the punctured ball by shrinking bands in quadratic integral
-- statement:
--   A Lévy-type measure with no atom at zero and locally integrable square admits quadratic band integral convergence as the inner cutoff tends to zero. Hence an upper bound shared by all band integrals transfers to the entire ball. This deterministic dominated-convergence lemma is the final step in the original LeanLevy small-ball variance inequality, directly supporting M5.

import Mathlib.Probability.Independence.CharacteristicFunction
open MeasureTheory Filter Topology

theorem levy_foundations_public_gaussian_band_exhaustion
    (ν : Measure ℝ) {r σ : ℝ}
    (hν_zero : ν {0} = 0)
    (hquad : IntegrableOn (fun x : ℝ => x ^ 2) {x | |x| < r} ν)
    {δ : ℕ → ℝ}
    (hδ : Filter.Tendsto δ Filter.atTop (nhds (0 : ℝ)))
    (hband : ∀ m, ∫ x in {x | δ m ≤ |x| ∧ |x| < r}, x ^ 2 ∂ν ≤ σ) :
    ∫ x in {x | |x| < r}, x ^ 2 ∂ν ≤ σ := by
  sorry
