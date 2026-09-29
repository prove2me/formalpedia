-- Prove2me | Theorems.Thm_mme_released_global_graded_hashed_recursive_construction
-- name    : mme_released_global_graded_hashed_recursive_construction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T18:14:58.985709+00:00
-- url     : https://prove2.me/theorems/90828c23-e435-4153-8138-6dc95b62e4a2
-- title:
--   Graded recursive construction on the hashed part of the released global candidate
-- statement:
--   The hashed half of the graded recursive construction for the released global candidate.
--
--   The global blocks split into two parts by the hash cell of each block. **Boundary cells** have a zero coordinate. **Hashed cells** are the 126 positive ones. The boundary part is closed by the exact-profile boundary end. This statement asks for the rest: a graded logarithmic joint recipe at level three on the **hashed part**, whose predicate `QPos` holds when every hashed block has its reference grade and every hashed cell's word histogram is within `eps` of the released profile.
--
--   Write $n = 6B$ with $B = D^5k^2$ blocks per owner, and let $Z$ be the dimension product of the boundary part's exact profiles. The expression in the statement is exactly what `mme_exact_profile_boundary_end` returns for that part. There are six positive tolerance caps with the following property. For every choice of smaller positive tolerances and every lower bound on $k$, some larger $k$ works as follows. For every admissible reference arrangement, the hashed part admits a recipe $R$ with $U_R \ge 1$, $Z\cdot abc \ge 1$, and
--
--   $$n\cdot 1.3223546 + \log U_R \le L_R, \qquad n\,(3\cdot 2.09612367517 - 10^{-7}) \le \log(Z \cdot abc).$$
--
--   Together with the published two-part split, this gives `mme_released_global_graded_joint_recursive_construction`. The boundary part adds no inputs and no rate, and it multiplies the dimensions by $Z$.
-- source:
--   Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, More Asymmetry Yields Faster Matrix Multiplication (https://arxiv.org/abs/2404.16349), sections 5-6: recursive regional hashing after the global extraction. Exact asymptotic statement as written.

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

theorem mme_released_global_graded_hashed_recursive_construction :
    ∃ eta : Fin 6 → ℝ, (∀ o, 0 < eta o) ∧
      ∀ eps : Fin 6 → ℝ, (∀ o, 0 < eps o) → (∀ o, eps o ≤ eta o) →
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
                    5 ^ (∑ s, zCountAt (k^2) c s * Boundary.ones s)) * (R.a * R.b * R.c) : ℕ) : ℝ) := by sorry
