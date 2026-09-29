-- Prove2me | solution 1 for mme_CW5_rate_237134_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T22:20:48.534407+00:00
-- url     : https://prove2.me/submissions/cf2cd5a4-478c-4c1d-a10e-1abcbb210846

import Theorems.Thm_mme_CW_repeated_power_rate_exponent_bound
import Theorems.Thm_mme_omega_eq_strassen

open MME BigOperators
universe u
set_option autoImplicit false

/-- The released rational weight parameter reduces the root exponent target to
an actual CW-five extraction and its strict normalized logarithmic surplus. -/
theorem solution
    {K : Type u} [Field K] (N inputs copies : ℕ)
    (hinputs : 0 < inputs) (a b c : Fin copies → ℕ) (rate : ℝ)
    (hrestrict : TensorObj.Restrict
      (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
      (TensorObj.bigAdd (fun _ : Fin inputs => (CWObj K 5).kronPow N)))
    (hweight : (inputs : ℝ) * Real.exp rate ≤
      ∑ j, ((a j * b j * c j : ℕ) : ℝ) ^ (3952233 / 5000000 : ℝ))
    (hsurplus : (N : ℝ) * Real.log 7 < rate) :
    matMulExp K < 237134 / 100000 := by
  rw [mme_omega_eq_strassen]
  have h := mme_CW_repeated_power_rate_exponent_bound 5 N inputs copies hinputs
    a b c (3952233 / 5000000) rate (by norm_num) hrestrict hweight (by
      simpa only [Nat.reduceAdd, Nat.cast_ofNat] using hsurplus)
  linarith


#print axioms solution
