-- Prove2me | Theorems.Thm_mme_joint_regional_CW_plan_omega_bound
-- name    : mme_joint_regional_CW_plan_omega_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T00:53:12.621967+00:00
-- url     : https://prove2.me/theorems/da406f19-105e-49fb-80a0-c3faeaeb886b
-- title:
--   Exponent bound from a surplus joint regional plan
-- statement:
--   Let $D$ be a joint regional plan on $N$ positions of $CW_5$ with $D.a\,D.b\,D.c \ge 1$, and let $\tau$ be real. If
--
--   $$D.\mathrm{inputs}\cdot 7^N \;<\; D.\mathrm{outputs}\cdot (D.a\,D.b\,D.c)^{\tau},$$
--
--   then over every field $K$ the matrix multiplication exponent satisfies $\omega(K) < 3\tau$.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v3: Theorem 5.3 (the global stage outputs one interface tensor over all six regions), Theorem 6.4 and Section 6.6 (each constituent stage divides every term into six regions, hashes each region jointly over all terms, and takes the tensor product of the six outputs), and Algorithm 1 in Section 7. https://arxiv.org/abs/2404.16349

import Definitions.Def_mme_joint_regional_CW_plan_data
import Definitions.Def_mme_omega
open MME MME.TensorObj MME.ProfiledCW
set_option autoImplicit false
universe u

theorem mme_joint_regional_CW_plan_omega_bound {K : Type u} [Field K] {N ell : ℕ} {P : Predicate N}
    (D : JointPlan N ell P) (tau : ℝ)
    (hvolume : 1 ≤ D.a * D.b * D.c)
    (hsurplus : ((D.inputs * 7 ^ N : ℕ) : ℝ) <
      (D.outputs : ℝ) * (((D.a * D.b * D.c : ℕ) : ℝ) ^ tau)) :
    matMulExp K < 3 * tau := by sorry
