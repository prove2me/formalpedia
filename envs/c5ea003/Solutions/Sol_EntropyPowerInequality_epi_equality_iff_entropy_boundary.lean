-- Prove2me | solution 1 for EntropyPowerInequality.epi_equality_iff_entropy_boundary
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:24:16.624182+00:00
-- url     : https://prove2.me/submissions/ebddc248-b818-4fef-8a61-08b3bc7d55fe

-- Sol generated from Probability/SharpBridge.lean
import Mathlib
import Definitions.Def_Probability_SharpBridge

/-!
# The sharp entropy-power / Euclidean-radius bridge

This file isolates the analytic core of the entropy power inequality (EPI).  If `h`
is a differential entropy in dimension `n`, its entropy radius and entropy power are

`r(h) = exp(h/n) / sqrt(2 π e)` and `N(h) = r(h)^2`.

Consequently the sharp EPI is exactly a Pythagorean (Euclidean `ℓ₂`) addition law
for entropy radii.  This is the exponent-two counterpart of the radius formulation
of Brunn--Minkowski.  We prove the equivalence, its exact equality condition, the
sharp isotropic-Gaussian case in every positive dimension, and an exact stability
identity measuring entropy excess above the sharp boundary.
-/

open Real

open EntropyPowerInequality







lemma normalization_pos : 0 < 2 * Real.pi * Real.exp 1 := by
  positivity




/-- Entropy power is strictly increasing in entropy in every positive dimension. -/
theorem entropyPower_strictMono {n : ℕ} (hn : 0 < n) :
    StrictMono (entropyPower n) := by
  intro a b hab
  unfold entropyPower
  apply div_lt_div_of_pos_right _ normalization_pos
  apply Real.exp_lt_exp.mpr
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  exact (div_lt_div_iff_of_pos_right hnR).2 (by linarith)











open EntropyPowerInequality in
theorem solution{n : ℕ} (hn : 0 < n)
    (hX hY hSum : ℝ) :
    entropyPower n hSum = entropyPower n hX + entropyPower n hY ↔
      hSum = sharpEntropyBoundary n hX hY := by
  have h_bound : entropyPower n (sharpEntropyBoundary n hX hY) = entropyPower n hX + entropyPower n hY := by
    unfold entropyPower sharpEntropyBoundary
    have h1 : 2 * ((n : ℝ) / 2 * Real.log (Real.exp (2 * hX / n) + Real.exp (2 * hY / n))) / n =
              Real.log (Real.exp (2 * hX / n) + Real.exp (2 * hY / n)) := by
      field_simp
    rw [h1]
    rw [Real.exp_log (by positivity : Real.exp (2 * hX / n) + Real.exp (2 * hY / n) > 0)]
    ring
  constructor
  · intro h
    exact (entropyPower_strictMono hn).injective (h.trans h_bound.symm)
  · intro h
    rw [h, h_bound]
