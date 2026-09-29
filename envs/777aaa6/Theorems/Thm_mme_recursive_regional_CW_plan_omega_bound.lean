-- Prove2me | Theorems.Thm_mme_recursive_regional_CW_plan_omega_bound
-- name    : mme_recursive_regional_CW_plan_omega_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T15:17:49.016154+00:00
-- url     : https://prove2.me/theorems/ce225d03-3917-4ea6-86c6-5dd8e6fb4652
-- title:
--   A charged regional CW recipe bounds the matrix-multiplication exponent
-- statement:
--   Let $D$ be a finite regional CW5 recipe on $N$ elementary positions, with $I$ input copies, $O$ output copies, and matrix dimensions $a,b,c$ satisfying $abc\ge1$. For any real $\tau$, if
--
--   $$I\,7^N < O(abc)^\tau,$$
--
--   then, over every field $K$,
--
--   $$\operatorname{matMulExp}(K)<3\tau.$$
--
--   The input-copy cost includes every type cover and regional product. The conclusion follows for the actual CW tensor, even when the recipe starts on a profile projection.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S7 , Section 7; finite copy-charged consequence of the recursive construction and asymptotic sum inequality.

import Definitions.Def_mme_recursive_regional_CW_data
import Definitions.Def_mme_omega
open MME MME.TensorObj MME.ProfiledCW
universe u
set_option autoImplicit false

theorem mme_recursive_regional_CW_plan_omega_bound {K : Type u} [Field K] {N ell : ℕ} {P : Predicate N}
    (D : RegionalPlan N ell P) (tau : ℝ)
    (hvolume : 1 ≤ D.a * D.b * D.c)
    (hsurplus : ((D.inputs * 7 ^ N : ℕ) : ℝ) <
      (D.outputs : ℝ) * (((D.a * D.b * D.c : ℕ) : ℝ) ^ tau)) :
    matMulExp K < 3 * tau := by sorry
