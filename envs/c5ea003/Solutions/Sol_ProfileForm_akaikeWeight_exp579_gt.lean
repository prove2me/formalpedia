-- Prove2me | solution 1 for ProfileForm.akaikeWeight_exp579_gt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:26:31.737697+00:00
-- url     : https://prove2.me/submissions/1eb733f6-aa08-4a9b-9bfa-392b5585b40b

-- Sol generated from NumberTheory/ProfileFormModelSelection.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormModelSelection
import Definitions.Def_NumberTheory_ProfileFormPowerLaw

/-!
# Profile form III: the model-selection verdict is a theorem, not a judgement

Context (experiment 579, paper 229; V1 rule).  The power-law profile won the
pre-registered model comparison with reported Akaike weight `0.9866` against
three rivals at `ΔAICc = +9.2` (exponential), `+11.5` (logistic, degenerate)
and `+16.9` (linear).

The Akaike weight of the best model in a four-model set with gaps
`d₁, d₂, d₃ ≥ 0` is

`w(d₁,d₂,d₃) = 1 / (1 + exp(-d₁/2) + exp(-d₂/2) + exp(-d₃/2))`.

Everything about the verdict except the fitted numbers is deterministic, and
that part is proved here:

* `akaikeWeight_mem_Ioo` — the weight is a genuine probability;
* `akaikeWeight_monotone_left` (and the symmetric variants) — widening any gap
  can only strengthen the winner;
* `akaikeWeight_lt_of_zero_gap` — a tied rival caps the weight at `1/2`, so a
  large weight is *evidence*, not an artefact of the normalisation;
* `akaikeWeight_ge_of_gaps` — a uniform lower bound `1/(1+3e^{-d/2})` in terms
  of the smallest gap;
* `akaikeWeight_exp579_gt` — with the measured gaps the weight exceeds `0.98`,
  confirming the reported `0.9866` to the accuracy that rigorous exponential
  bounds allow;
* `akaikeWeight_tendsto_one` — the weight saturates at `1` as the gaps grow.

The numerical bounds rest only on `Real.exp_one_gt_d9` and `Real.add_one_le_exp`
(`exp_four_ge`, `exp_neg_le_inv`); the file shares the `ProfileForm` namespace
with `NumberTheory.ProfileFormPowerLaw`.
-/

open ProfileForm

open Real Filter Topology


theorem akaikeWeight_denom_pos (d₁ d₂ d₃ : ℝ) :
    0 < 1 + Real.exp (-d₁ / 2) + Real.exp (-d₂ / 2) + Real.exp (-d₃ / 2) := by
  have h1 := Real.exp_pos (-d₁ / 2)
  have h2 := Real.exp_pos (-d₂ / 2)
  have h3 := Real.exp_pos (-d₃ / 2)
  linarith







/-- A rigorous numerical lower bound for `exp 4`. -/
theorem exp_four_ge : (54.59 : ℝ) ≤ Real.exp 4 := by
  have h : Real.exp 4 = (Real.exp 1) ^ (4:ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hpow := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) he.le 4
  rw [h]
  nlinarith [hpow]

/-- Turning a lower bound on `exp y` into an upper bound on `exp (-y)`. -/
theorem exp_neg_le_inv {y c : ℝ} (hc : 0 < c) (h : c ≤ Real.exp y) :
    Real.exp (-y) ≤ c⁻¹ := by
  rw [Real.exp_neg]
  exact inv_anti₀ hc h




open ProfileForm in
theorem solution: 0.98 < akaikeWeight 9.2 11.5 16.9 := by
  have hd := akaikeWeight_denom_pos 9.2 11.5 16.9
  have he4 := exp_four_ge
  have b1 : Real.exp (-9.2 / 2) ≤ 0.0115 := by
    have hE : Real.exp (4.6 : ℝ) = Real.exp 4 * Real.exp (0.6 : ℝ) := by
      rw [← Real.exp_add]; norm_num
    have h06 : (1.6 : ℝ) ≤ Real.exp (0.6 : ℝ) := by
      have := Real.add_one_le_exp (0.6 : ℝ); linarith
    have hbig : (87 : ℝ) ≤ Real.exp (4.6 : ℝ) := by
      rw [hE]
      calc (87:ℝ) ≤ 54.59 * 1.6 := by norm_num
        _ ≤ Real.exp 4 * Real.exp (0.6:ℝ) :=
            mul_le_mul he4 h06 (by norm_num) (by positivity)
    have hrw : (-9.2 / 2 : ℝ) = -(4.6 : ℝ) := by norm_num
    rw [hrw]
    have := exp_neg_le_inv (by norm_num : (0:ℝ) < 87) hbig
    calc Real.exp (-(4.6:ℝ)) ≤ (87:ℝ)⁻¹ := this
      _ ≤ 0.0115 := by norm_num
  have b2 : Real.exp (-11.5 / 2) ≤ 0.0067 := by
    have hE : Real.exp (5.75 : ℝ) = Real.exp 4 * Real.exp (1.75 : ℝ) := by
      rw [← Real.exp_add]; norm_num
    have h175 : (2.75 : ℝ) ≤ Real.exp (1.75 : ℝ) := by
      have := Real.add_one_le_exp (1.75 : ℝ); linarith
    have hbig : (150 : ℝ) ≤ Real.exp (5.75 : ℝ) := by
      rw [hE]
      calc (150:ℝ) ≤ 54.59 * 2.75 := by norm_num
        _ ≤ Real.exp 4 * Real.exp (1.75:ℝ) :=
            mul_le_mul he4 h175 (by norm_num) (by positivity)
    have hrw : (-11.5 / 2 : ℝ) = -(5.75 : ℝ) := by norm_num
    rw [hrw]
    calc Real.exp (-(5.75:ℝ)) ≤ (150:ℝ)⁻¹ :=
          exp_neg_le_inv (by norm_num) hbig
      _ ≤ 0.0067 := by norm_num
  have b3 : Real.exp (-16.9 / 2) ≤ 0.00034 := by
    have hmono : Real.exp (-16.9 / 2) ≤ Real.exp (-(8:ℝ)) := by
      apply Real.exp_le_exp.mpr; norm_num
    have hE : Real.exp (8 : ℝ) = Real.exp 4 * Real.exp 4 := by
      rw [← Real.exp_add]; norm_num
    have hbig : (2980 : ℝ) ≤ Real.exp (8 : ℝ) := by
      rw [hE]
      calc (2980:ℝ) ≤ 54.59 * 54.59 := by norm_num
        _ ≤ Real.exp 4 * Real.exp 4 :=
            mul_le_mul he4 he4 (by norm_num) (by positivity)
    have := exp_neg_le_inv (by norm_num : (0:ℝ) < 2980) hbig
    calc Real.exp (-16.9 / 2) ≤ Real.exp (-(8:ℝ)) := hmono
      _ ≤ (2980:ℝ)⁻¹ := this
      _ ≤ 0.00034 := by norm_num
  rw [akaikeWeight, lt_div_iff₀ hd]
  linarith
