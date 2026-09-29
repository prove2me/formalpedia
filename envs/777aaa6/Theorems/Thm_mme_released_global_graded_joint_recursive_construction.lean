-- Prove2me | Theorems.Thm_mme_released_global_graded_joint_recursive_construction
-- name    : mme_released_global_graded_joint_recursive_construction
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-22T21:21:52.154815+00:00
-- url     : https://prove2.me/theorems/55bde106-3adc-41ac-bbd9-8e89d799a028
-- title:
--   Core graded recursive construction for the released global candidate
-- statement:
--   Construct the graded-source logarithmic joint recipe required by the released global candidate. This is the core recursive continuation obligation: it supplies positive tolerance caps, a common sufficiently large scale, a graded joint recipe for every admissible reference arrangement, and the two explicit logarithmic budget inequalities. It is the construction layer used by the parent continuation theorem.
-- source:
--   Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, https://arxiv.org/abs/2404.16349, Sections 5-6

import Definitions.Def_mme_released_global_joint_interface
import Definitions.Def_mme_graded_integer_regional_step_data
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RegionRealization MME.ReleasedGlobal
set_option autoImplicit false

theorem mme_released_global_graded_joint_recursive_construction :
    ∃ eta : Fin 6 → ℝ, (∀ o, 0 < eta o) ∧
      ∀ eps : Fin 6 → ℝ, (∀ o, 0 < eps o) → (∀ o, eps o ≤ eta o) →
        ∀ k0 : ℕ, ∃ k : ℕ, k0 ≤ k ∧
          ∀ (hk : 0 < k^2) (a : ∀ o : Fin 6, Reference o (k^2)),
            ∃ R : LogJointRecipeG (4 * (6 * blocks (k^2))) 3 (jointWindow (k^2) hk a eps),
              1 ≤ R.inputs ∧ 1 ≤ R.a * R.b * R.c ∧
              (6 * blocks (k^2) : ℝ) * ((13223546 : ℝ)/10000000) +
                Real.log (R.inputs : ℝ) ≤ R.logOutputs ∧
              (6 * blocks (k^2) : ℝ) *
                (3 * ((209612367517 : ℝ)/100000000000) - 1/10000000) ≤
                  Real.log ((R.a * R.b * R.c : ℕ) : ℝ) := by sorry
