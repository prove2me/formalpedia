-- Prove2me | Theorems.Thm_mme_released_global_graded_hashed_recursive_construction_caps_one
-- name    : mme_released_global_graded_hashed_recursive_construction_caps_one
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T09:43:54.680665+00:00
-- url     : https://prove2.me/theorems/b4f708f1-b8d2-4ac8-a8b2-7c5e2c584426
-- title:
--   Fixed-cap graded construction on the hashed part
-- statement:
--   For every positive tolerance profile bounded by 1, all sufficiently large squared dimensions and every admissible reference arrangement admit a level-three logarithmic joint recipe for the hashed region. The recipe satisfies the same input, weighted-dimension, output-rate, and dimension-rate bounds as the released-global hashed construction. This fixed-cap theorem is the analytic core used by the parent statement, which chooses the cap profile identically equal to 1.
-- source:
--   Reduction subgoal for mme_released_global_graded_hashed_recursive_construction; based on Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349, sections 5–6

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

theorem mme_released_global_graded_hashed_recursive_construction_caps_one :
    (eps : Fin 6 → ℝ) → (∀ o, 0 < eps o) → (∀ o, eps o ≤ 1) →
      ∀ k0 : ℕ, ∃ k : ℕ, k0 ≤ k ∧
        ∀ (hk : 0 < k^2) (a : ∀ o : Fin 6, Reference o (k^2)),
          ∃ R : LogJointRecipeG (partSize (k^2) a 1) 3 (QPos (k^2) a eps),
            1 ≤ R.inputs ∧
            1 ≤ (∏ c : Fin zCells,
                  ((Fintype.card {p : Fin (zCount (k^2) a) // zCellOf (k^2) a p = c}).factorial /
                    ∏ s, (zCountAt (k^2) c s).factorial) *
                  5 ^ (∑ s, zCountAt (k^2) c s * Boundary.ones s)) * (R.a * R.b * R.c) ∧
            (6 * blocks (k^2) : ℝ) * ((13223546 : ℝ)/10000000) +
              Real.log (R.inputs : ℝ) ≤ R.logOutputs ∧
            (6 * blocks (k^2) : ℝ) *
              (3 * ((209612367517 : ℝ)/100000000000) - 1/10000000) ≤
                Real.log (((∏ c : Fin zCells,
                  ((Fintype.card {p : Fin (zCount (k^2) a) // zCellOf (k^2) a p = c}).factorial /
                    ∏ s, (zCountAt (k^2) c s).factorial) *
                  5 ^ (∑ s, zCountAt (k^2) c s * Boundary.ones s)) *
                    (R.a * R.b * R.c) : ℕ) : ℝ) := by sorry
