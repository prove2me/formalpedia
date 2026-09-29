-- Prove2me | Theorems.Thm_mme_global_CW_graded_start_omega_bound
-- name    : mme_global_CW_graded_start_omega_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T15:45:00.59712+00:00
-- url     : https://prove2.me/theorems/b818d040-9bd7-46bd-94f8-ef88f4ade849
-- title:
--   Exponent bound from a surplus graded global start
-- statement:
--   Let `D` be a graded global start on `M` positions with `D.a * D.b * D.c >= 1`, and let `tau` be real. If `D.inputs * 7^M < exp(D.logOutputs) * (D.a * D.b * D.c)^tau`, then over every field the matrix multiplication exponent is less than `3 tau`.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v3: interface tensors fix the level structure exactly and let only complete-split distributions vary (Definitions 3.6 and 4.1); Theorem 6.4, Section 6.6 and Algorithm 1 chain the stages. https://arxiv.org/abs/2404.16349

import Definitions.Def_mme_global_CW_graded_start_data
import Definitions.Def_mme_omega
open MME MME.TensorObj MME.GlobalCW
set_option autoImplicit false
universe u

theorem mme_global_CW_graded_start_omega_bound {K : Type u} [Field K] {M ell : ℕ} (D : GlobalCW.StartG M ell)
    (tau : ℝ) (hvolume : 1 ≤ D.a * D.b * D.c)
    (hsurplus : ((D.inputs * 7 ^ M : ℕ) : ℝ) <
      Real.exp D.logOutputs * (((D.a * D.b * D.c : ℕ) : ℝ) ^ tau)) :
    matMulExp K < 3 * tau := by sorry
