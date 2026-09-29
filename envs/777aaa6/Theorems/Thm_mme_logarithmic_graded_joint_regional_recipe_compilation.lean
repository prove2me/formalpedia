-- Prove2me | Theorems.Thm_mme_logarithmic_graded_joint_regional_recipe_compilation
-- name    : mme_logarithmic_graded_joint_regional_recipe_compilation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T15:43:11.294911+00:00
-- url     : https://prove2.me/theorems/f5e36f0c-1d31-47bd-b45a-619c960a1ccd
-- title:
--   Graded logarithmic joint recipes compile to joint regional plans
-- statement:
--   A graded logarithmic joint recipe is the logarithmic joint regional recipe with graded-source integer steps in its stages. Every graded logarithmic joint recipe `D` compiles to a joint regional plan `A` with the same inputs and dimensions and with `exp(D.logOutputs) <= A.outputs`.
--
--   Graded-source steps are what let hashing stages chain. An integer step's source must contain its typical band. The previous exact stage's outputs fix every parent block's shape, so they can only cover the parent-graded part of that band.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v3: interface tensors fix the level structure exactly and let only complete-split distributions vary (Definitions 3.6 and 4.1); Theorem 6.4, Section 6.6 and Algorithm 1 chain the stages. https://arxiv.org/abs/2404.16349

import Definitions.Def_mme_joint_regional_CW_plan_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Mathlib
open BigOperators MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem mme_logarithmic_graded_joint_regional_recipe_compilation {N ell : ℕ} {P : Predicate N} (D : LogJointRecipeG N ell P) :
    ∃ A : JointPlan N ell P,
      A.inputs = D.inputs ∧ Real.exp D.logOutputs ≤ (A.outputs : ℝ) ∧ A.dims = D.dims := by sorry
