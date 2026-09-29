-- Prove2me | Theorems.Thm_mme_more_asymmetry_released_witness_joint_log_recipe
-- name    : mme_more_asymmetry_released_witness_joint_log_recipe
-- status  : Open
-- author  : @marwahaha
-- created : 2026-09-22T00:54:57.320972+00:00
-- url     : https://prove2.me/theorems/69643de3-4a90-4ec6-ab32-ba37832ec707
-- title:
--   Released More Asymmetry witness: finite logarithmic joint recipe
-- statement:
--   There is a finite logarithmic joint recipe for the released $q=5$ More Asymmetry witness on $4n$ original copies of $CW_5$, with $n>0$, at least one input, and positive matrix volume. Its certified rates satisfy
--
--   $$\log(\mathrm{outputs}) - \log(\mathrm{inputs}) \;\ge\; n\,(2.81302098456 - 10^{-6})$$
--
--   and
--
--   $$\log(abc) \;\ge\; n\,(3\cdot 2.09612367517 - 10^{-7}).$$
--
--   This restates the released-witness finite log recipe target with joint regional stages. The released parameters of More Asymmetry (osf.io/mw5ak, `data/W1.00_2.371339.mat`) hash each level-3 region jointly over the terms of all six global regions (Theorem 6.4), and hash the level-2 stage jointly over all terms. A plain logarithmic recipe cannot rejoin partition parts. With these parameters that costs about $1.7\cdot10^{-2}$ per $n$ at level 3 alone, far above the $10^{-6}$ budget. With joint stages the paper's construction has the required shape.
--
--   Two tasks remain beyond this reformulation. The global stage (Theorem 5.3) must also be expressed, and the recipe must be instantiated from the released parameters with exact certified rates.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v3: Theorem 5.3 (the global stage outputs one interface tensor over all six regions), Theorem 6.4 and Section 6.6 (each constituent stage divides every term into six regions, hashes each region jointly over all terms, and takes the tensor product of the six outputs), and Algorithm 1 in Section 7. https://arxiv.org/abs/2404.16349

import Definitions.Def_mme_logarithmic_joint_regional_CW_recipe
open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem mme_more_asymmetry_released_witness_joint_log_recipe :
    ∃ (n ell : ℕ) (P : Predicate (4 * n)) (D : LogJointRecipe (4 * n) ell P),
      0 < n ∧ 1 ≤ D.inputs ∧ 1 ≤ D.a * D.b * D.c ∧
      (n : ℝ) * ((281302098456 : ℝ) / 100000000000 - 1 / 1000000) +
          Real.log (D.inputs : ℝ) ≤ D.logOutputs ∧
      (n : ℝ) * (3 * ((209612367517 : ℝ) / 100000000000) - 1 / 10000000) ≤
          Real.log ((D.a * D.b * D.c : ℕ) : ℝ) := by sorry
