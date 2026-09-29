-- Prove2me | solution 1 for mme_stothers_phi233_stationary_marginal_address_entropy_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:50:18.27228+00:00
-- url     : https://prove2.me/submissions/0523e7a6-9017-4a28-8d94-6f8194b3af6a

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_mme_stothers_phi233_profile_data
import Theorems.Thm_mme_stothers_phi233_marginal_address_entropy_upper
import Theorems.Thm_mme_stothers_phi233_entropy_tangent_stability

open MME

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true

/-- A positive stationary profile gives the sharp entropy exponent for the
whole `phi_233` same-marginal completion family. -/
theorem solution
    (N alpha beta gamma delta : ℕ) (hN : 0 < N)
    (sigma mu a b c d : ℝ)
    (hsigma0 : 0 < sigma) (hsigmaUpper : sigma < 2 / 3)
    (hmu0 : 0 < mu) (hmuUpper : mu < 1 / 2)
    (hsigmaRatio : ((2 * alpha + beta : ℕ) : ℝ) / (N : ℝ) = sigma)
    (hmuRatio : ((alpha + gamma : ℕ) : ℝ) / (N : ℝ) = mu)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (htotal : 2 * a + b + c + d = 1)
    (hab : 2 * a + b = sigma) (hac : a + c = mu)
    (hstation :
      2 * (-Real.log (a / 2) - 1) -
          2 * (-Real.log (b / 2) - 1) -
          (-Real.log (c / 2) - 1) +
          (-Real.log (d / 2) - 1) = 0) :
    (Nat.card
        (MME.StothersFourth.Phi233.MarginalAddress
          N alpha beta gamma delta) : ℝ) ≤
      (((2 * N + 1 : ℕ) : ℝ)) ^ 10 *
        Real.exp (((2 * N : ℕ) : ℝ) *
          (4 * Real.negMulLog (a / 2) +
            2 * Real.negMulLog (b / 2) +
            2 * Real.negMulLog (c / 2) +
            2 * Real.negMulLog (d / 2))) := by
  let E : ℝ := mu / (1 - mu)
  let H : ℝ := sigma / (2 * (1 - sigma))
  have hmu1 : mu < 1 := lt_trans hmuUpper (by norm_num)
  have hsigma1 : sigma < 1 := lt_trans hsigmaUpper (by norm_num)
  have hE : 0 < E := by
    dsimp only [E]
    exact div_pos hmu0 (sub_pos.mpr hmu1)
  have hH : 0 < H := by
    dsimp only [H]
    exact div_pos hsigma0
      (mul_pos (by norm_num) (sub_pos.mpr hsigma1))
  have hEL : E < 1 := by
    dsimp only [E]
    apply (div_lt_one (by linarith)).2
    linarith
  have hHL : H < 1 := by
    dsimp only [H]
    apply (div_lt_one
      (mul_pos (by norm_num) (sub_pos.mpr hsigma1))).2
    linarith
  have hSigmaIdentity : 2 * H / (2 * H + 1) = sigma := by
    dsimp only [H]
    field_simp [ne_of_gt (by linarith : 0 < 1 - sigma)]
    ring
  have hMuIdentity : E / (E + 1) = mu := by
    dsimp only [E]
    field_simp [ne_of_gt (by linarith : 0 < 1 - mu)]
    ring
  obtain ⟨a', b', c', d', ha', hb', hc', hd', htotal', hab', hac', hcard⟩ :=
    mme_stothers_phi233_marginal_address_entropy_upper
      N alpha beta gamma delta hN E H 1 hE hH hEL hHL
      (hsigmaRatio.trans hSigmaIdentity.symm)
      (hmuRatio.trans hMuIdentity.symm)
  have hab'' : 2 * a' + b' = sigma := hab'.trans hSigmaIdentity
  have hac'' : a' + c' = mu := hac'.trans hMuIdentity
  have hentropy := mme_stothers_phi233_entropy_tangent_stability
    a b c d a' b' c' d' sigma mu sigma mu
    ha hb hc hd ha' hb' hc' hd' htotal htotal'
    hab hac hab'' hac'' hstation
  have hentropy' :
      4 * Real.negMulLog (a' / 2) +
            2 * Real.negMulLog (b' / 2) +
            2 * Real.negMulLog (c' / 2) +
            2 * Real.negMulLog (d' / 2) ≤
        4 * Real.negMulLog (a / 2) +
            2 * Real.negMulLog (b / 2) +
            2 * Real.negMulLog (c / 2) +
            2 * Real.negMulLog (d / 2) := by
    simpa using hentropy
  have hexp :
      Real.exp (((2 * N : ℕ) : ℝ) *
          (4 * Real.negMulLog (a' / 2) +
            2 * Real.negMulLog (b' / 2) +
            2 * Real.negMulLog (c' / 2) +
            2 * Real.negMulLog (d' / 2))) ≤
        Real.exp (((2 * N : ℕ) : ℝ) *
          (4 * Real.negMulLog (a / 2) +
            2 * Real.negMulLog (b / 2) +
            2 * Real.negMulLog (c / 2) +
            2 * Real.negMulLog (d / 2))) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hentropy' (by positivity)
  exact hcard.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
