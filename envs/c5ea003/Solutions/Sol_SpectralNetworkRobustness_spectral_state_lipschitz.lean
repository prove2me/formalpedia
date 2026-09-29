-- Prove2me | solution 1 for SpectralNetworkRobustness.spectral_state_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:55:40.742834+00:00
-- url     : https://prove2.me/submissions/7bffe3ea-0be7-40b8-8689-aafaddc64a13

-- Sol generated from Geometry/SpectralNetworkRobustness.lean
import Mathlib
import Definitions.Def_Geometry_SpectralNetworkRobustness

/-!
# Spectral graph control and certified robustness

This file isolates a precise, non-vacuous version of the proposed connection.
A graph spectral gap controls the squared variation of an internal computation
state; a Lipschitz readout then converts that control into an end-to-end
Lipschitz bound, which yields a certified classification radius.

It also formalizes two contrarian negative results: algebraic connectivity alone
cannot control either a network's Lipschitz constant or its robustness radius.
A gain bound and a positive output margin are both indispensable.
-/

open SpectralNetworkRobustness














open SpectralNetworkRobustness in
theorem solution    {connectivity gain : ℝ} {h : ℝ → ℝ}
    (hc : 0 < connectivity) (hg : 0 ≤ gain)
    (hs : SpectralStateBound connectivity gain h) :
    LipschitzBound h (gain / Real.sqrt connectivity) := by
  intro x y
  have h1 : connectivity * (h x - h y) ^ 2 ≤ gain ^ 2 * (x - y) ^ 2 := hs x y
  have h2 : (h x - h y) ^ 2 ≤ (gain ^ 2 / connectivity) * (x - y) ^ 2 := by
    have := h1
    rw [div_mul_eq_mul_div]
    rw [le_div_iff₀ hc]
    linarith
  have h3 : (h x - h y) ^ 2 ≤ ((gain / Real.sqrt connectivity) * (x - y)) ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (le_of_lt hc)]
    exact h2
  have h4 : |h x - h y| ≤ |gain / Real.sqrt connectivity * (x - y)| := by
    rwa [sq_le_sq] at h3
  have h5 : |gain / Real.sqrt connectivity * (x - y)| = gain / Real.sqrt connectivity * |x - y| := by
    rw [abs_mul, abs_of_nonneg (div_nonneg hg (Real.sqrt_nonneg _))]
  rw [h5] at h4
  exact h4
