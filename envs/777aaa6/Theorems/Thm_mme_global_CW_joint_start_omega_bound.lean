-- Prove2me | Theorems.Thm_mme_global_CW_joint_start_omega_bound
-- name    : mme_global_CW_joint_start_omega_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T07:28:25.351212+00:00
-- url     : https://prove2.me/theorems/37ad72f9-2a0f-4193-803a-dfebc6653e4f
-- title:
--   Exponent bound from a finite global start and joint continuation
-- statement:
--   A strict finite CW surplus for a global start with joint continuation implies the matrix multiplication exponent is strictly less than three times the surplus exponent.
-- source:
--   Finite global extraction for More Asymmetry Proposition 5.1 and Theorem 5.3.

import Definitions.Def_mme_global_CW_joint_start_data
import Definitions.Def_mme_omega
open MME MME.TensorObj MME.GlobalCW
set_option autoImplicit false
universe u

theorem mme_global_CW_joint_start_omega_bound {K : Type u} [Field K] {M ell : ℕ} (D : GlobalCW.Start M ell)
    (tau : ℝ) (hvolume : 1 ≤ D.a * D.b * D.c)
    (hsurplus : ((D.inputs * 7 ^ M : ℕ) : ℝ) <
      Real.exp D.logOutputs * (((D.a * D.b * D.c : ℕ) : ℝ) ^ tau)) :
    matMulExp K < 3 * tau := by
  sorry
