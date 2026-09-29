-- Prove2me | solution 1 for Catalog.Novelty.QuantCurvature.quadExcess_le_curvatureBound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:18:51.937684+00:00
-- url     : https://prove2.me/submissions/520a5e2e-8b4a-471c-8d74-e8a24994f79f

-- Sol generated from Novelty/QuantCurvatureNoFloor.lean
import Mathlib
import Definitions.Def_Novelty_QuantCurvatureNoFloor
import Definitions.Def_Novelty_WeightQuantFloorLadder

/-!
# Curvature explains the weight ladder: a `4`-per-bit ceiling and no intrinsic floor

Companion to `Novelty.WeightQuantFloorLadder` (NET-95).  The measured k-quant
ladder obeys a geometric law with per-bit factor in `[5/2, 3]`.  This file gives
the structural model that *predicts* such a law, and proves the two statements
that dissolve the alleged "sub-6-bit floor".

**The model.**  Near a trained optimum the loss increase caused by a weight
perturbation `e` is, to second order, the quadratic form
`quadExcess lam e = ½ ∑ᵢ λᵢ eᵢ²` in the Hessian eigenbasis.  A `b`-bit quantiser
with dynamic-range constant `c` produces `|eᵢ| ≤ c / 2 ^ b`.  Hence

  `quadExcess ≤ (n Λ c² / 2) / 4 ^ b = curvatureBound K b`.

**Two consequences.**

* `curvatureBound_per_bit` — the model's degradation is multiplied by *exactly*
  `4` per bit removed.  So `4` is the theoretical ceiling of the per-bit rate,
  and `measured_ladder_beats_curvature_ceiling` records that the measured ladder
  stays strictly below it at every pair of rungs (observed rates `2.54`–`2.98`):
  calibration-aware k-quants beat the naive curvature prediction.
* `quantizer_quality_is_a_bit_shift` — a quantiser that is `2 ^ j` times more
  accurate is worth *exactly* `j` bits: the degradation bound at bit width `b`
  with constant `c / 2 ^ j` equals the bound at width `b + j` with constant `c`.
  Combined with `no_intrinsic_floor` (for any bit width and any tolerance there
  is a quantiser quality meeting the tolerance *at that width*) this is the NET-95
  law in formal form: **the floor is a property of (quantiser quality × scale),
  never of the bit width alone.**

Finally `curvatureBound_convexOn` shows the model curve is convex in the bit
width — the "gentle convex curve" of the measurement — and `no_bit_width_floor`
shows that in this model no finite bit width is undeployable.
-/

open Catalog.Novelty.QuantCurvature

open Finset Catalog.Novelty.WeightQuantFloor

/-! ## 1. The second-order model -/





/-! ## 2. The `4`-per-bit ceiling -/






/-! ## 3. Quantiser quality is a bit shift -/



/-! ## 4. The measurement versus the ceiling -/



open Catalog.Novelty.QuantCurvature in
theorem solution{n : ℕ} (lam e : Fin n → ℝ) (Λ c : ℝ) (b : ℕ)
    (hlam : ∀ i, 0 ≤ lam i) (hΛ : ∀ i, lam i ≤ Λ)
    (he : ∀ i, |e i| ≤ c / 2 ^ b) :
    quadExcess lam e ≤ curvatureBound (n * Λ * c ^ 2 / 2) b := by
  have hterm : ∀ i ∈ Finset.univ, lam i * e i ^ 2 ≤ Λ * (c ^ 2 / 4 ^ b) := by
    intro i _
    have h1 : e i ^ 2 ≤ (c / 2 ^ b) ^ 2 := by
      have := abs_nonneg (e i)
      nlinarith [he i, abs_nonneg (e i), sq_abs (e i)]
    have h2 : (c / 2 ^ b : ℝ) ^ 2 = c ^ 2 / 4 ^ b := by
      rw [div_pow]
      congr 1
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    calc lam i * e i ^ 2 ≤ lam i * (c ^ 2 / 4 ^ b) := by
          rw [h2] at h1
          exact mul_le_mul_of_nonneg_left h1 (hlam i)
      _ ≤ Λ * (c ^ 2 / 4 ^ b) := by
          have : (0:ℝ) ≤ c ^ 2 / 4 ^ b := by positivity
          exact mul_le_mul_of_nonneg_right (hΛ i) this
  have hsum : ∑ i, lam i * e i ^ 2 ≤ (n : ℝ) * (Λ * (c ^ 2 / 4 ^ b)) := by
    have := Finset.sum_le_sum hterm
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  have h4 : (0:ℝ) < 4 ^ b := by positivity
  have hgoal : (n : ℝ) * (Λ * (c ^ 2 / 4 ^ b)) = 2 * ((n * Λ * c ^ 2 / 2) / 4 ^ b) := by
    field_simp
  rw [quadExcess, curvatureBound]
  linarith [hsum, hgoal]
