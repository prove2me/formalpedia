-- Prove2me | solution 1 for SpectralNetworkRobustness.spectral_connectivity_certified_radius
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:57:59.457245+00:00
-- url     : https://prove2.me/submissions/f7cdc8aa-0eb7-479f-865d-ca46abbfe2dc

-- Sol generated from Geometry/SpectralNetworkRobustness.lean
import Mathlib
import Definitions.Def_Geometry_SpectralNetworkRobustness
import Theorems.Thm_SpectralNetworkRobustness_spectral_state_lipschitz

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








/-- Lipschitz constants multiply through a scalar readout. -/
theorem readout_composition_lipschitz
    {h readout : ℝ → ℝ} {stateGain readoutGain : ℝ}
    (hs : LipschitzBound h stateGain)
    (hr : LipschitzBound readout readoutGain)
    (hrg : 0 ≤ readoutGain) :
    LipschitzBound (fun x => readout (h x)) (readoutGain * stateGain) := by
  intro x y
  have h1 : |readout (h x) - readout (h y)| ≤ readoutGain * |h x - h y| := hr (h x) (h y)
  have h2 : |h x - h y| ≤ stateGain * |x - y| := hs x y
  calc |readout (h x) - readout (h y)| ≤ readoutGain * |h x - h y| := h1
    _ ≤ readoutGain * (stateGain * |x - y|) := by nlinarith
    _ = readoutGain * stateGain * |x - y| := by ring

/-- The standard margin-over-Lipschitz certificate for a positive binary score. -/
theorem margin_over_lipschitz_certifies
    {f : ℝ → ℝ} {x margin L : ℝ}
    (hm : f x = margin) (hmargin : 0 < margin)
    (hL : 0 < L) (hf : LipschitzBound f L) :
    CertifiedPositive f x (margin / L) := by
  intro y hy
  have h1 : |f y - f x| ≤ L * |y - x| := hf y x
  have h2 : f y ≥ f x - L * |y - x| := by
    have := abs_le.mp h1
    linarith
  rw [hm] at h2
  have h3 : L * |y - x| < margin := by
    calc L * |y - x| < L * (margin / L) := by nlinarith
      _ = margin := by field_simp
  linarith





open SpectralNetworkRobustness in
theorem solution    {connectivity stateGain readoutGain margin x : ℝ}
    {state readout : ℝ → ℝ}
    (hc : 0 < connectivity) (hsg : 0 < stateGain)
    (hrg : 0 < readoutGain) (hm : 0 < margin)
    (hs : SpectralStateBound connectivity stateGain state)
    (hr : LipschitzBound readout readoutGain)
    (hx : readout (state x) = margin) :
    CertifiedPositive (fun z => readout (state z)) x
      (margin * Real.sqrt connectivity / (readoutGain * stateGain)) := by
  -- First, derive Lipschitz bound for state from spectral bound
  have hstateLip : LipschitzBound state (stateGain / Real.sqrt connectivity) :=
    spectral_state_lipschitz hc (le_of_lt hsg) hs
  -- Compose with readout to get Lipschitz bound for full function
  have hfullLip : LipschitzBound (fun z => readout (state z))
      (readoutGain * (stateGain / Real.sqrt connectivity)) :=
    readout_composition_lipschitz hstateLip hr (le_of_lt hrg)
  -- Now use margin_over_lipschitz_certifies
  -- L = readoutGain * stateGain / sqrt(connectivity)
  -- radius = margin / L = margin * sqrt(connectivity) / (readoutGain * stateGain)
  have hL_pos : 0 < readoutGain * (stateGain / Real.sqrt connectivity) := by
    exact mul_pos hrg (div_pos hsg (Real.sqrt_pos.mpr hc))
  have hradius_eq : margin * Real.sqrt connectivity / (readoutGain * stateGain) =
      margin / (readoutGain * (stateGain / Real.sqrt connectivity)) := by
    field_simp
  rw [hradius_eq]
  exact margin_over_lipschitz_certifies hx hm hL_pos hfullLip
