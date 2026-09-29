-- Prove2me | solution 1 for mme_stothers_phi134_entropy_rate_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T09:39:07.499181+00:00
-- url     : https://prove2.me/submissions/26192d77-0bef-466d-8815-9a61d03c1a28

import Mathlib
import Definitions.Def_mme_stothers_fourth_data

open MME Real

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

/-- The entropy of the three marginal word classes for the symmetric
`phi_134` profile, normalized by the even tensor-power length `2N`. -/
noncomputable def phi134MarginalEntropy
    (sigma a c : ℝ) : ℝ :=
  (3 - c) * Real.log 2 +
    Real.negMulLog sigma + Real.negMulLog (1 - sigma) +
    Real.negMulLog a + Real.negMulLog c +
    Real.negMulLog (1 - a - c)

/-- The marginal entropy plus the eight component values is exactly the
profile-parametric rate printed in Davie--Stothers Lemma 5.1(iii).  The proof
also covers the allowed boundary `1-a-c=0`, using the `0^0=1` convention of
real powers. -/
theorem phi134_entropy_rate_identity_aux
    (sigma a c L E H : ℝ)
    (ha : 0 < a) (hc : 0 < c)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1)
    (hL : 0 < L) (hE : 0 < E) (hH : 0 < H) :
    phi134MarginalEntropy sigma a c +
          sigma * Real.log L +
          ((1 - sigma) + (1 - a - c)) * Real.log E +
          c * Real.log H =
      Real.log
        (8 *
          ((L / sigma) ^ sigma *
            (E / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((H / 2) / c) ^ c *
            (E / (1 - a - c)) ^ (1 - a - c))) := by
  have hsigma : 0 < sigma := lt_of_lt_of_le hc hcs
  have honesigma : 0 < 1 - sigma := by linarith
  have ht : 0 ≤ 1 - a - c := by linarith
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have h8 : (8 : ℝ) ≠ 0 := by norm_num
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  by_cases ht0 : 1 - a - c = 0
  · unfold phi134MarginalEntropy
    rw [ht0]
    simp
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_rpow (by positivity : 0 < L / sigma),
      Real.log_rpow (by positivity : 0 < E / (1 - sigma)),
      Real.log_rpow (by positivity : 0 < a⁻¹),
      Real.log_rpow (by positivity : 0 < (H / 2) / c),
      Real.log_div hL.ne' hsigma.ne',
      Real.log_div hE.ne' honesigma.ne',
      Real.log_inv a,
      Real.log_div (div_ne_zero hH.ne' h2) hc.ne',
      Real.log_div hH.ne' h2, hlog8]
    unfold Real.negMulLog
    norm_num
    ring

  · have htpos : 0 < 1 - a - c := lt_of_le_of_ne ht (Ne.symm ht0)
    unfold phi134MarginalEntropy
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_rpow (by positivity : 0 < L / sigma),
      Real.log_rpow (by positivity : 0 < E / (1 - sigma)),
      Real.log_rpow (by positivity : 0 < 1 / a),
      Real.log_rpow (by positivity : 0 < (H / 2) / c),
      Real.log_rpow (by positivity : 0 < E / (1 - a - c)),
      Real.log_div hL.ne' hsigma.ne',
      Real.log_div hE.ne' honesigma.ne',
      Real.log_div one_ne_zero ha.ne',
      Real.log_div (div_ne_zero hH.ne' h2) hc.ne',
      Real.log_div hH.ne' h2,
      Real.log_div hE.ne' htpos.ne', Real.log_one, hlog8]
    unfold Real.negMulLog
    norm_num
    ring

theorem solution
    (sigma a c L E H : ℝ)
    (ha : 0 < a) (hc : 0 < c)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1)
    (hL : 0 < L) (hE : 0 < E) (hH : 0 < H) :
    ((3 - c) * Real.log 2 +
        Real.negMulLog sigma + Real.negMulLog (1 - sigma) +
        Real.negMulLog a + Real.negMulLog c +
        Real.negMulLog (1 - a - c)) +
          sigma * Real.log L +
          ((1 - sigma) + (1 - a - c)) * Real.log E +
          c * Real.log H =
      Real.log
        (8 *
          ((L / sigma) ^ sigma *
            (E / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((H / 2) / c) ^ c *
            (E / (1 - a - c)) ^ (1 - a - c))) := by
  change phi134MarginalEntropy sigma a c +
          sigma * Real.log L +
          ((1 - sigma) + (1 - a - c)) * Real.log E +
          c * Real.log H = _
  exact phi134_entropy_rate_identity_aux
    sigma a c L E H ha hc hcs hsa hL hE hH
