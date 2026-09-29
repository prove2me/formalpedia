-- Prove2me | Theorems.Thm_mme_more_asymmetry_global_graded_finite_witness
-- name    : mme_more_asymmetry_global_graded_finite_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T15:45:49.860783+00:00
-- url     : https://prove2.me/theorems/13380552-4954-495a-b877-70f75bf79af2
-- title:
--   Released More Asymmetry witness: graded global joint finite recipe
-- statement:
--   There exist `n > 0`, a level `ell` and a graded global start `D` on `4n` positions of `CW_5` with at least one input and positive matrix volume, such that
--
--   `n (2.81302098456 - 10^-6) + log(inputs) <= logOutputs`
--
--   and
--
--   `n (3 * 2.09612367517 - 10^-7) <= log(a b c)`.
--
--   This is the global joint finite witness with graded-source constituent steps. The released More Asymmetry parameters (published as exact rationals in `mme_more_asymmetry_released_parameters_data`) meet both rates exactly, with slack of about `10^-6` and `10^-7` for finite-length losses.
--
--   The graded form is needed for the construction to chain its stages. With ordinary integer steps, the source of each constituent stage must contain its whole typical band, including words in which a few parent blocks have the wrong shape. The global stage's exact outputs fix every block's shape, so they cannot cover such words. Enumerating nearby shape patterns as extra types is ruled out by the divisibility requirement on split counts.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v3: interface tensors fix the level structure exactly and let only complete-split distributions vary (Definitions 3.6 and 4.1); Theorem 6.4, Section 6.6 and Algorithm 1 chain the stages. https://arxiv.org/abs/2404.16349

import Definitions.Def_mme_global_CW_graded_start_data
open MME MME.GlobalCW
set_option autoImplicit false

theorem mme_more_asymmetry_global_graded_finite_witness :
    ∃ (n ell : ℕ) (D : GlobalCW.StartG (4 * n) ell),
      0 < n ∧ 1 ≤ D.inputs ∧ 1 ≤ D.a * D.b * D.c ∧
      (n : ℝ) * ((281302098456 : ℝ) / 100000000000 - 1 / 1000000) +
        Real.log D.inputs ≤ D.logOutputs ∧
      (n : ℝ) * (3 * ((209612367517 : ℝ) / 100000000000) - 1 / 10000000) ≤
        Real.log ((D.a * D.b * D.c : ℕ) : ℝ) := by sorry
