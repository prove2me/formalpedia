-- Prove2me | solution 1 for ProfileForm.uniformResidual_three_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:06:32.362983+00:00
-- url     : https://prove2.me/submissions/fb4a7c03-7fb9-4c3a-b8f3-b5d6f1c47e60

-- Sol generated from NumberTheory/ProfileFormUniformMixturePeak.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormPowerLaw
import Definitions.Def_NumberTheory_ProfileFormResidualPeak
import Definitions.Def_NumberTheory_ProfileFormUniformMixturePeak

/-!
# Profile form VII: even the Dickman surrogate humps — outside the window

Second Stage-4 (Critic) result of this cycle, sharper than the two-atom
counterexample of `ProfileFormMixturePeak`.

The mixture-Dickman baseline actually used in the analysis is the *uniform*
scale mixture `M(x) = (1 - e^{-x})/x`.  On the measured window `x ∈ [0,1]` the
residual `T/M` of a power law against it is decreasing, which is why the
observed hump looks like new physics.  But the crossing of the two competing
log-slopes `b/(1+x)` (from the profile) and `1/x - 1/(e^x - 1)` (from the
mixture) happens near `x ≈ 10`, and there the residual really does peak.

We prove this for the measured exponent `b = 11/10`:

`uniformResidual 3 < uniformResidual 10` and `uniformResidual 100 <
uniformResidual 10`,

hence `uniformResidual` attains an interior maximum on `[3, 100]` and is neither
monotone nor antitone there (`uniformResidual_peak`).

Consequence (`peak_is_window_dependent`): *peakedness of the residual is a
window-relative statement*, not an intrinsic property distinguishing the
baseline.  Combined with `ProfileFormResidualPeak.peak_forces_nonPowerLaw_baseline`,
the defensible reading of the experiment is: the measured hump at `x ≈ 0.59`
locates a feature *inside* the analysed window, and its interpretation must be
tied to that window.

The numerical work is done with the rational-exponent trick
`rpow_eleven_tenths_le` / `le_rpow_eleven_tenths`, which converts a bound on
`a ^ (11/10)` into an exact comparison of integer powers.
-/

open ProfileForm

open Set

/-! ## Interior maxima on a general window -/




/-! ## Rational exponents as integer power comparisons -/


theorem le_rpow_eleven_tenths {a c : ℝ} (ha : 0 ≤ a)
    (h : c ^ (10:ℕ) ≤ a ^ (11:ℕ)) : c ≤ a ^ ((11:ℝ)/10) := by
  have hpow : (a ^ ((11:ℝ)/10)) ^ (10:ℕ) = a ^ (11:ℕ) := by
    rw [← Real.rpow_natCast (a ^ ((11:ℝ)/10)) 10, ← Real.rpow_mul ha,
      ← Real.rpow_natCast a 11]
    norm_num
  have hnn : 0 ≤ a ^ ((11:ℝ)/10) := Real.rpow_nonneg ha _
  have hle : c ^ (10:ℕ) ≤ (a ^ ((11:ℝ)/10)) ^ (10:ℕ) := by rw [hpow]; exact h
  exact le_of_pow_le_pow_left₀ (by norm_num) hnn hle

/-! ## The residual against the uniform (Dickman surrogate) mixture -/


theorem uniformResidual_eq {x : ℝ} (hx : 0 < x) :
    uniformResidual x = (1 + x) ^ (-(11:ℝ)/10) * x / (1 - Real.exp (-x)) := by
  have h1 : (0:ℝ) < 1 - Real.exp (-x) := by
    have : Real.exp (-x) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  simp only [uniformResidual, powerProfile, dickmanMixtureBaseline, one_mul]
  rw [div_div_eq_mul_div]
  ring_nf

theorem exp_three_ge : (20 : ℝ) ≤ Real.exp 3 := by
  have h := Real.exp_one_gt_d9
  have hsplit : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  rw [hsplit]
  nlinarith [Real.exp_pos (1:ℝ)]









open ProfileForm in
theorem solution: uniformResidual 3 ≤ 69/100 := by
  have hbase : (1:ℝ) + 3 = 4 := by norm_num
  have hkey : (229/50 : ℝ) ≤ (4:ℝ) ^ ((11:ℝ)/10) := by
    apply le_rpow_eleven_tenths (by norm_num)
    norm_num
  have hpos : (0:ℝ) < (4:ℝ) ^ ((11:ℝ)/10) := Real.rpow_pos_of_pos (by norm_num) _
  have hrpow : (4:ℝ) ^ (-(11:ℝ)/10) ≤ 50/229 := by
    have hinv : (4:ℝ) ^ (-(11:ℝ)/10) = ((4:ℝ) ^ ((11:ℝ)/10))⁻¹ := by
      rw [← Real.rpow_neg (by norm_num)]
      ring_nf
    rw [hinv, inv_le_comm₀ hpos (by norm_num)]
    calc (50/229 : ℝ)⁻¹ = 229/50 := by norm_num
      _ ≤ (4:ℝ) ^ ((11:ℝ)/10) := hkey
  have hexp : Real.exp (-(3:ℝ)) ≤ 1/20 := by
    have := exp_three_ge
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have hden : (19/20 : ℝ) ≤ 1 - Real.exp (-(3:ℝ)) := by linarith
  have hdenpos : (0:ℝ) < 1 - Real.exp (-(3:ℝ)) := by linarith
  rw [uniformResidual_eq (by norm_num), hbase, div_le_iff₀ hdenpos]
  have hrp : (0:ℝ) < (4:ℝ) ^ (-(11:ℝ)/10) := Real.rpow_pos_of_pos (by norm_num) _
  nlinarith
