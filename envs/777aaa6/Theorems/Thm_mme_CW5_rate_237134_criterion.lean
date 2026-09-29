-- Prove2me | Theorems.Thm_mme_CW5_rate_237134_criterion
-- name    : mme_CW5_rate_237134_criterion
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T16:25:24.582517+00:00
-- url     : https://prove2.me/theorems/17c9488d-c9d0-4071-8a28-64e524d8f999
-- title:
--   A CW-five rate surplus implies the precise root bound
-- statement:
--   An actual extraction at weight parameter 3952233 over 5000000, with positive source multiplicity and normalized rate strictly above N log 7, implies matMulExp is below 237134 over 100000. The required surplus remains a separate numerical obligation. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_CW_repeated_power_rate_exponent_bound
import Theorems.Thm_mme_omega_eq_strassen
open MME BigOperators
universe u

theorem mme_CW5_rate_237134_criterion
    {K : Type u} [Field K] (N inputs copies : ℕ)
    (hinputs : 0 < inputs) (a b c : Fin copies → ℕ) (rate : ℝ)
    (hrestrict : TensorObj.Restrict
      (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
      (TensorObj.bigAdd (fun _ : Fin inputs => (CWObj K 5).kronPow N)))
    (hweight : (inputs : ℝ) * Real.exp rate ≤
      ∑ j, ((a j * b j * c j : ℕ) : ℝ) ^ (3952233 / 5000000 : ℝ))
    (hsurplus : (N : ℝ) * Real.log 7 < rate) :
    matMulExp K < 237134 / 100000 := by sorry
