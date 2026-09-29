-- Prove2me | solution 1 for mme_CW_auxiliary_numeric_2376
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-23T23:39:48.80629+00:00
-- url     : https://prove2.me/submissions/0763b5d9-d1c5-4364-a1a1-3542d2e0363a

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The numerical endpoint in Coppersmith--Winograd's Section 8

This file isolates the transcendental numerical calculation used at `q = 6`.
All five parameters and `tau` are exact rationals.  Logarithms are enclosed by
the odd-power series for `log ((1+x)/(1-x))`; the only library decimal bound
used is Mathlib's proved ten-decimal enclosure for `log 2`.
-/

open BigOperators Finset

namespace MME.CW90NumericEndpoint

/-- Twice the first `n` terms of the odd-power series for `atanh z`. -/
noncomputable def logLower (n : ℕ) (z : ℝ) : ℝ :=
  2 * ∑ i ∈ range n, z ^ (2 * i + 1) / (2 * i + 1)

/-- The corresponding explicit upper bound for `log ((1+z)/(1-z))`. -/
noncomputable def logUpper (n : ℕ) (z : ℝ) : ℝ :=
  logLower n z + 2 * z ^ (2 * n + 1) / (1 - z ^ 2)

lemma logLower_le_log_ratio (n : ℕ) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    logLower n z ≤ Real.log ((1 + z) / (1 - z)) := by
  have h := Real.sum_range_le_log_div hz0 hz1 n
  unfold logLower
  linarith

lemma log_ratio_le_logUpper (n : ℕ) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Real.log ((1 + z) / (1 - z)) ≤ logUpper n z := by
  have h := Real.log_div_le_sum_range_add hz0 hz1 n
  unfold logUpper logLower
  calc
    Real.log ((1 + z) / (1 - z)) = 2 * (1 / 2 * Real.log ((1 + z) / (1 - z))) := by ring
    _ ≤ 2 * ((∑ i ∈ range n, z ^ (2 * i + 1) / (2 * i + 1)) +
        z ^ (2 * n + 1) / (1 - z ^ 2)) := by gcongr
    _ = 2 * ∑ i ∈ range n, z ^ (2 * i + 1) / (2 * i + 1) +
        2 * z ^ (2 * n + 1) / (1 - z ^ 2) := by ring

/-- The exact rational parameters used below.  Notice that the denominator of
`d` is `3 * 10^6`, so the normalization is exact, not rounded. -/
noncomputable def tau : ℝ := 99 / 125
noncomputable def a : ℝ := 233 / 1000000
noncomputable def b : ℝ := 12506 / 1000000
noncomputable def c : ℝ := 102546 / 1000000
noncomputable def d : ℝ := 616627 / (3 * 1000000)

theorem parameter_normalization : 3 * a + 6 * b + 3 * c + 3 * d = 1 := by
  norm_num [a, b, c, d]
  rfl

/-- The Section 8 right-hand side, specialized only in its arity `q = 6`. -/
noncomputable def rhs : ℝ :=
  (12 : ℝ) ^ (6 * tau * b) *
      (38 : ℝ) ^ (3 * tau * c) *
      (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) ^ d /
    ((2 * a + 2 * b + c) ^ (2 * a + 2 * b + c) *
      (2 * b + 2 * d) ^ (2 * b + 2 * d) *
      (2 * c + d) ^ (2 * c + d) *
      (2 * b) ^ (2 * b) * a ^ a)

private noncomputable def log2Lower : ℝ := 6931471803 / 10000000000
private noncomputable def log2Upper : ℝ := 6931471808 / 10000000000

private lemma log2Lower_lt : log2Lower < Real.log 2 := by
  unfold log2Lower
  convert Real.log_two_gt_d9 using 1
  norm_num1

private lemma log2_lt_log2Upper : Real.log 2 < log2Upper := by
  unfold log2Upper
  convert Real.log_two_lt_d9 using 1
  norm_num1

private lemma log12_lower :
    3 * log2Lower + logLower 8 (1 / 5) < Real.log 12 := by
  have hs := logLower_le_log_ratio 8 (z := (1 / 5 : ℝ)) (by norm_num) (by norm_num)
  norm_num at hs
  rw [show (12 : ℝ) = 2 ^ 3 * (3 / 2) by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow]
  have h2 := log2Lower_lt
  norm_num at h2 ⊢
  linarith

private lemma log38_lower :
    5 * log2Lower + logLower 8 (3 / 35) < Real.log 38 := by
  have hs := logLower_le_log_ratio 8 (z := (3 / 35 : ℝ)) (by norm_num) (by norm_num)
  norm_num at hs
  rw [show (38 : ℝ) = 2 ^ 5 * (19 / 16) by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  have h2 := log2Lower_lt
  norm_num at h2 ⊢
  linarith

private lemma log6_lower :
    2 * log2Lower + logLower 8 (1 / 5) < Real.log 6 := by
  have hs := logLower_le_log_ratio 8 (z := (1 / 5 : ℝ)) (by norm_num) (by norm_num)
  norm_num at hs
  rw [show (6 : ℝ) = 2 ^ 2 * (3 / 2) by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow]
  have h2 := log2Lower_lt
  norm_num at h2 ⊢
  linarith

private lemma log7261_lower :
    6 * log2Lower + logLower 8 (861 / 13661) < Real.log (7261 / 100) := by
  have hs := logLower_le_log_ratio 8 (z := (861 / 13661 : ℝ)) (by norm_num) (by norm_num)
  norm_num at hs
  rw [show (7261 / 100 : ℝ) = 2 ^ 6 * (7261 / 6400) by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  have h2 := log2Lower_lt
  norm_num at h2 ⊢
  linarith

private lemma log_s1_upper :
    Real.log (2 * a + 2 * b + c) <
      logUpper 8 (189 / 15814) - 3 * log2Lower := by
  have hs := log_ratio_le_logUpper 8 (z := (189 / 15814 : ℝ)) (by norm_num) (by norm_num)
  have h2 := log2Lower_lt
  rw [show 2 * a + 2 * b + c = (16003 / 15625 : ℝ) / 2 ^ 3 by norm_num [a, b, c],
    Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num at hs h2 ⊢
  linarith

private lemma log_s2_upper :
    Real.log (2 * b + 2 * d) <
      logUpper 8 (55829 / 205829) - 2 * log2Lower := by
  have hs := log_ratio_le_logUpper 8 (z := (55829 / 205829 : ℝ)) (by norm_num) (by norm_num)
  have h2 := log2Lower_lt
  rw [show 2 * b + 2 * d = (130829 / 75000 : ℝ) / 2 ^ 2 by norm_num [b, d],
    Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num at hs h2 ⊢
  linarith

private lemma log_s3_upper :
    Real.log (2 * c + d) <
      logUpper 8 (481903 / 1981903) - 2 * log2Lower := by
  have hs := log_ratio_le_logUpper 8 (z := (481903 / 1981903 : ℝ)) (by norm_num) (by norm_num)
  have h2 := log2Lower_lt
  rw [show 2 * c + d = (1231903 / 750000 : ℝ) / 2 ^ 2 by norm_num [c, d],
    Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num at hs h2 ⊢
  linarith

private lemma log_2b_upper :
    Real.log (2 * b) < logUpper 8 (9387 / 40637) - 6 * log2Lower := by
  have hs := log_ratio_le_logUpper 8 (z := (9387 / 40637 : ℝ)) (by norm_num) (by norm_num)
  have h2 := log2Lower_lt
  rw [show 2 * b = (25012 / 15625 : ℝ) / 2 ^ 6 by norm_num [b],
    Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num at hs h2 ⊢
  linarith

private lemma log_a_upper :
    Real.log a < logUpper 8 (14199 / 45449) - 13 * log2Lower := by
  have hs := log_ratio_le_logUpper 8 (z := (14199 / 45449 : ℝ)) (by norm_num) (by norm_num)
  have h2 := log2Lower_lt
  rw [show a = (29824 / 15625 : ℝ) / 2 ^ 13 by norm_num [a],
    Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num at hs h2 ⊢
  linarith

private lemma log7061_upper :
    Real.log (7061 / 100) < 6 * log2Upper + logUpper 8 (661 / 13461) := by
  have hs := log_ratio_le_logUpper 8 (z := (661 / 13461 : ℝ)) (by norm_num) (by norm_num)
  have h2 := log2_lt_log2Upper
  rw [show (7061 / 100 : ℝ) = 2 ^ 6 * (7061 / 6400) by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  norm_num at hs h2 ⊢
  linarith

private lemma rpow6_lower : (7061 / 100 : ℝ) < (6 : ℝ) ^ (297 / 125 : ℝ) := by
  rw [Real.lt_rpow_iff_log_lt (by norm_num) (by norm_num)]
  have h6 := log6_lower
  have h7061 := log7061_upper
  have hcert :
      6 * log2Upper + logUpper 8 (661 / 13461) <
        (297 / 125 : ℝ) * (2 * log2Lower + logLower 8 (1 / 5)) := by
    norm_num [log2Lower, log2Upper, logLower, logUpper, Finset.sum_range_succ]
  norm_num at h6 h7061 ⊢
  nlinarith

private noncomputable def certificateLower : ℝ :=
  6 * tau * b * (3 * log2Lower + logLower 8 (1 / 5)) +
  3 * tau * c * (5 * log2Lower + logLower 8 (3 / 35)) +
  d * (2 * log2Lower + 3 * tau * (2 * log2Lower + logLower 8 (1 / 5)) +
    (6 * log2Lower + logLower 8 (861 / 13661))) -
  (2 * a + 2 * b + c) * (logUpper 8 (189 / 15814) - 3 * log2Lower) -
  (2 * b + 2 * d) * (logUpper 8 (55829 / 205829) - 2 * log2Lower) -
  (2 * c + d) * (logUpper 8 (481903 / 1981903) - 2 * log2Lower) -
  (2 * b) * (logUpper 8 (9387 / 40637) - 6 * log2Lower) -
  a * (logUpper 8 (14199 / 45449) - 13 * log2Lower)

/-- A purely rational certificate.  Expanding the eight-term sums reduces this
to exact normalization of a positive rational number. -/
theorem exact_rational_certificate : 6 * log2Upper < certificateLower := by
  norm_num [certificateLower, tau, a, b, c, d, log2Lower, log2Upper, logLower, logUpper,
    Finset.sum_range_succ]

private noncomputable def logRhs : ℝ :=
  (6 * tau * b) * Real.log 12 +
  (3 * tau * c) * Real.log 38 +
  d * Real.log (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) -
  (2 * a + 2 * b + c) * Real.log (2 * a + 2 * b + c) -
  (2 * b + 2 * d) * Real.log (2 * b + 2 * d) -
  (2 * c + d) * Real.log (2 * c + d) -
  (2 * b) * Real.log (2 * b) - a * Real.log a

private lemma central_log_lower :
    2 * log2Lower + 3 * tau * (2 * log2Lower + logLower 8 (1 / 5)) +
        (6 * log2Lower + logLower 8 (861 / 13661)) <
      Real.log (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) := by
  have h2 := log2Lower_lt
  have h6 := log6_lower
  have h7261 := log7261_lower
  have hx := rpow6_lower
  have hxpos : 0 < (6 : ℝ) ^ (3 * tau) := by positivity
  have ht : 0 < 3 * tau := by norm_num [tau]
  have harg : (7261 / 100 : ℝ) < (6 : ℝ) ^ (3 * tau) + 2 := by
    norm_num [tau] at hx ⊢
    linarith
  have hlast : Real.log (7261 / 100 : ℝ) < Real.log ((6 : ℝ) ^ (3 * tau) + 2) :=
    Real.log_lt_log (by norm_num) harg
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.log_pow, Real.log_rpow (by norm_num)]
  norm_num at h2 ⊢
  nlinarith

private lemma certificateLower_lt_logRhs : certificateLower < logRhs := by
  have h12 := log12_lower
  have h38 := log38_lower
  have hcentral := central_log_lower
  have hs1 := log_s1_upper
  have hs2 := log_s2_upper
  have hs3 := log_s3_upper
  have h2b := log_2b_upper
  have ha := log_a_upper
  have ht1 : 0 < 6 * tau * b := by norm_num [tau, b]
  have ht2 : 0 < 3 * tau * c := by norm_num [tau, c]
  have hd : 0 < d := by norm_num [d]
  have hp1 : 0 < 2 * a + 2 * b + c := by norm_num [a, b, c]
  have hp2 : 0 < 2 * b + 2 * d := by norm_num [b, d]
  have hp3 : 0 < 2 * c + d := by norm_num [c, d]
  have hp4 : 0 < 2 * b := by norm_num [b]
  have hp5 : 0 < a := by norm_num [a]
  have hterm1 := mul_lt_mul_of_pos_left h12 ht1
  have hterm2 := mul_lt_mul_of_pos_left h38 ht2
  have hterm3 := mul_lt_mul_of_pos_left hcentral hd
  have hterm4 := neg_lt_neg (mul_lt_mul_of_pos_left hs1 hp1)
  have hterm5 := neg_lt_neg (mul_lt_mul_of_pos_left hs2 hp2)
  have hterm6 := neg_lt_neg (mul_lt_mul_of_pos_left hs3 hp3)
  have hterm7 := neg_lt_neg (mul_lt_mul_of_pos_left h2b hp4)
  have hterm8 := neg_lt_neg (mul_lt_mul_of_pos_left ha hp5)
  unfold certificateLower logRhs
  linarith

private lemma log_rhs : Real.log rhs = logRhs := by
  unfold rhs logRhs tau a b c d
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by norm_num), Real.log_rpow (by norm_num), Real.log_rpow (by positivity),
    Real.log_rpow (by positivity), Real.log_rpow (by positivity), Real.log_rpow (by positivity),
    Real.log_rpow (by positivity), Real.log_rpow (by positivity)]
  ring

/-- The strict numerical inequality used at the CW90 endpoint
`3 * tau = 297/125 = 2.376`. -/
theorem sixty_four_lt_rhs : (64 : ℝ) < rhs := by
  have hlog2 : 6 * Real.log 2 < 6 * log2Upper :=
    mul_lt_mul_of_pos_left log2_lt_log2Upper (by norm_num)
  have hlogs : Real.log 64 < Real.log rhs := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow, log_rhs]
    exact hlog2.trans (exact_rational_certificate.trans certificateLower_lt_logRhs)
  exact (Real.log_lt_log_iff (by norm_num) (by unfold rhs tau a b c d; positivity)).mp hlogs

/-- Expanded form of `sixty_four_lt_rhs`, suitable for direct use as the
strict numerical half of the Section 8 endpoint argument. -/
theorem cw90_q6_tau_99_125 :
    (64 : ℝ) <
      (12 : ℝ) ^ (6 * (99 / 125 : ℝ) * (12506 / 1000000 : ℝ)) *
          (38 : ℝ) ^ (3 * (99 / 125 : ℝ) * (102546 / 1000000 : ℝ)) *
          (4 * (6 : ℝ) ^ (3 * (99 / 125 : ℝ)) *
            ((6 : ℝ) ^ (3 * (99 / 125 : ℝ)) + 2)) ^ (616627 / (3 * 1000000) : ℝ) /
        ((2 * (233 / 1000000 : ℝ) + 2 * (12506 / 1000000 : ℝ) +
              (102546 / 1000000 : ℝ)) ^
            (2 * (233 / 1000000 : ℝ) + 2 * (12506 / 1000000 : ℝ) +
              (102546 / 1000000 : ℝ)) *
          (2 * (12506 / 1000000 : ℝ) + 2 * (616627 / (3 * 1000000) : ℝ)) ^
            (2 * (12506 / 1000000 : ℝ) + 2 * (616627 / (3 * 1000000) : ℝ)) *
          (2 * (102546 / 1000000 : ℝ) + (616627 / (3 * 1000000) : ℝ)) ^
            (2 * (102546 / 1000000 : ℝ) + (616627 / (3 * 1000000) : ℝ)) *
          (2 * (12506 / 1000000 : ℝ)) ^ (2 * (12506 / 1000000 : ℝ)) *
          (233 / 1000000 : ℝ) ^ (233 / 1000000 : ℝ)) := by
  simpa [rhs, tau, a, b, c, d] using sixty_four_lt_rhs

end MME.CW90NumericEndpoint

open MME

/-- Platform wrapper for the exact `q = 6`, `tau = 99/125` auxiliary
certificate. -/
theorem solution :
    (64 : ℝ) <
      (12 : ℝ) ^ (6 * (99 / 125 : ℝ) * (12506 / 1000000 : ℝ)) *
          (38 : ℝ) ^ (3 * (99 / 125 : ℝ) * (102546 / 1000000 : ℝ)) *
          (4 * (6 : ℝ) ^ (3 * (99 / 125 : ℝ)) *
            ((6 : ℝ) ^ (3 * (99 / 125 : ℝ)) + 2)) ^ (616627 / (3 * 1000000) : ℝ) /
        ((2 * (233 / 1000000 : ℝ) + 2 * (12506 / 1000000 : ℝ) +
              (102546 / 1000000 : ℝ)) ^
            (2 * (233 / 1000000 : ℝ) + 2 * (12506 / 1000000 : ℝ) +
              (102546 / 1000000 : ℝ)) *
          (2 * (12506 / 1000000 : ℝ) + 2 * (616627 / (3 * 1000000) : ℝ)) ^
            (2 * (12506 / 1000000 : ℝ) + 2 * (616627 / (3 * 1000000) : ℝ)) *
          (2 * (102546 / 1000000 : ℝ) + (616627 / (3 * 1000000) : ℝ)) ^
            (2 * (102546 / 1000000 : ℝ) + (616627 / (3 * 1000000) : ℝ)) *
          (2 * (12506 / 1000000 : ℝ)) ^ (2 * (12506 / 1000000 : ℝ)) *
          (233 / 1000000 : ℝ) ^ (233 / 1000000 : ℝ)) := by
  exact MME.CW90NumericEndpoint.cw90_q6_tau_99_125
