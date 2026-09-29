-- Prove2me | Theorems.Thm_mme_logarithmic_joint_regional_recipe_compilation
-- name    : mme_logarithmic_joint_regional_recipe_compilation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T00:54:11.098893+00:00
-- url     : https://prove2.me/theorems/5af814d3-dc6b-41af-9b34-bf38b1f25cbb
-- title:
--   Logarithmic joint recipes compile to joint regional plans
-- statement:
--   A logarithmic joint recipe is a logarithmic regional recipe extended by joint regional stages. Within a stage, each part uses integer steps with a common certified logarithmic copy budget. The stage's logarithmic output is the sum of the part budgets plus that of the continuation.
--
--   Every logarithmic joint recipe $D$ compiles to a joint regional plan $A$ with the same inputs and dimensions and with $e^{D.\mathrm{logOutputs}} \le A.\mathrm{outputs}$.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v3: Theorem 5.3 (the global stage outputs one interface tensor over all six regions), Theorem 6.4 and Section 6.6 (each constituent stage divides every term into six regions, hashes each region jointly over all terms, and takes the tensor product of the six outputs), and Algorithm 1 in Section 7. https://arxiv.org/abs/2404.16349

import Definitions.Def_mme_joint_regional_CW_plan_data
import Definitions.Def_mme_logarithmic_joint_regional_CW_recipe
import Mathlib
open BigOperators MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem mme_logarithmic_joint_regional_recipe_compilation {N ell : ℕ} {P : Predicate N} (D : LogJointRecipe N ell P) :
    ∃ A : JointPlan N ell P,
      A.inputs = D.inputs ∧ Real.exp D.logOutputs ≤ (A.outputs : ℝ) ∧ A.dims = D.dims := by sorry
