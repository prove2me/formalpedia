-- Prove2me | Theorems.Thm_mme_CW_copied_finite_surplus_omega_bound
-- name    : mme_CW_copied_finite_surplus_omega_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T14:53:38.309213+00:00
-- url     : https://prove2.me/theorems/a348a5be-0b52-4a9e-ad54-8d05b41d31bf
-- title:
--   A fully charged finite CW surplus bounds the matrix exponent
-- statement:
--   Suppose inputs copies of CW5 to power N restrict to outputs copies of the matrix tensor <a,b,c>, with a*b*c at least one. If outputs*(a*b*c)^tau is strictly larger than inputs*7^N, then the matrix multiplication exponent is strictly below 3*tau. Every source copy is included in the right-hand cost; no subexponential overhead is silently omitted.
-- source:
--   Finite constructive realization of Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 , Proposition 6.3 and Theorems 6.2 and 6.4; Section 7 for conversion to an exponent bound. This theorem retains explicit finite combinatorial hypotheses and input-copy costs. It does not supply the paper numerical parameter witness.

import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_tensor_rank
open MME MME.TensorObj
universe u
set_option autoImplicit false

theorem mme_CW_copied_finite_surplus_omega_bound {K : Type u} [Field K]
    (N inputs outputs a b c : ℕ) (tau : ℝ) (hvolume : 1 ≤ a * b * c)
    (hextract : Restrict (bigAdd (fun _ : Fin outputs ↦ MMObj K a b c))
      (bigAdd (fun _ : Fin inputs ↦ (CWObj K 5).kronPow N)))
    (hsurplus : ((inputs * 7 ^ N : ℕ) : ℝ) <
      (outputs : ℝ) * (((a * b * c : ℕ) : ℝ) ^ tau)) :
    matMulExp K < 3 * tau := by sorry
