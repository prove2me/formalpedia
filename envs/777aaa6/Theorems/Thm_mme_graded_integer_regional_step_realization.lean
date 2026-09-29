-- Prove2me | Theorems.Thm_mme_graded_integer_regional_step_realization
-- name    : mme_graded_integer_regional_step_realization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T15:42:21.72308+00:00
-- url     : https://prove2.me/theorems/f6e7005b-9209-4e2e-84d3-a6eec151b4cd
-- title:
--   Graded-source integer steps realize as exact steps
-- statement:
--   A graded-source integer step consists of an ordinary integer step over a band predicate `B`, together with the fact that every parent-graded `B`-word lies in the actual source `P`. Every graded-source integer step realizes as an exact step with source `P`. The exact step has at least as many guaranteed copies as the integer step and the same output.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v3: interface tensors fix the level structure exactly and let only complete-split distributions vary (Definitions 3.6 and 4.1); Theorem 6.4, Section 6.6 and Algorithm 1 chain the stages. https://arxiv.org/abs/2404.16349

import Definitions.Def_mme_graded_integer_regional_step_data
open MME MME.RegionRealization MME.ProfiledCW
set_option autoImplicit false

theorem mme_graded_integer_regional_step_realization {ell M : ℕ} {P : ProfiledCW.Predicate M} (D : IntegerStepG ell M P) :
    ∃ E : ExactStep ell M P, D.step.copies ≤ E.copies ∧ E.output = D.step.output := by sorry
