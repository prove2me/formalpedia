-- Prove2me | Theorems.Thm_mme_released_global_graded_hashed_recursive_construction_scalar_cap_hashed
-- name    : mme_released_global_graded_hashed_recursive_construction_scalar_cap_hashed
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T22:51:26.380989+00:00
-- url     : https://prove2.me/theorems/5f83bcf1-af4e-41da-89a4-510ec5a0eea4
-- title:
--   Scalar-tolerance hashed construction with the boundary charged at its unit-scale rate
-- statement:
--   This is the hashed-part form of the scalar-tolerance graded construction. The exact dimension factor of the boundary blocks is replaced by its unit-scale lower bound.
--
--   Let $B$ be the explicit unit-scale boundary factor of `mme_released_boundary_dimension_factor_power`:
--
--   $$B=\prod_{c}\binom{\sum_s n^{(1)}_{c,s}}{(n^{(1)}_{c,s})_s}\,5^{\sum_s n^{(1)}_{c,s}\,\mathrm{ones}(s)}.$$
--
--   **Statement.** For every tolerance $0<e\le1$ and every $k_0$ there is $k\ge k_0$ with the following property. For every admissible reference arrangement $a$ at scale $k^2$, there is a level-three graded logarithmic joint recipe $R$ on the hashed part with source $\mathrm{QPos}(k^2,a,e)$ such that $\operatorname{inputs}(R)\ge1$, $R.a\,R.b\,R.c\ge1$,
--
--   $$6\,\mathrm{blocks}(k^2)\cdot 1.3223546+\log\operatorname{inputs}(R)\le\operatorname{logOutputs}(R),$$
--
--   $$6\,\mathrm{blocks}(k^2)\bigl(3\cdot 2.09612367517-10^{-7}\bigr)\le k^2\log B+\log\bigl(R.a\,R.b\,R.c\bigr).$$
--
--   Compared with `mme_released_global_graded_hashed_recursive_construction_scalar_cap`, the recipe's own dimensions now meet the target net of a fixed boundary contribution $k^2\log B$. The recipe no longer has to handle the exact multinomial factor of the boundary blocks. Since $B^{k^2}\le Z_{k^2}(a)$, this statement implies the scalar-cap statement. It asks for slightly more: $\log Z_{k^2}-k^2\log B$ is polynomial in the number of cell-word pairs times $\log$ of the counts, which is negligible against the $10^{-7}$ slack per block.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 5-7; dimension accounting of the boundary (zero-cell) blocks for the released fourth-power parameters (Section 7).

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

theorem mme_released_global_graded_hashed_recursive_construction_scalar_cap_hashed :
    ∀ e : ℝ, 0 < e → e ≤ 1 →
      ∀ k0 : ℕ, ∃ k : ℕ, k0 ≤ k ∧
        ∀ (hk : 0 < k^2) (a : ∀ o : Fin 6, Reference o (k^2)),
          ∃ R : LogJointRecipeG (partSize (k^2) a 1) 3 (QPos (k^2) a (fun _ ↦ e)),
            1 ≤ R.inputs ∧
            1 ≤ R.a * R.b * R.c ∧
            (6 * blocks (k^2) : ℝ) * ((13223546 : ℝ)/10000000) +
              Real.log (R.inputs : ℝ) ≤ R.logOutputs ∧
            (6 * blocks (k^2) : ℝ) *
              (3 * ((209612367517 : ℝ)/100000000000) - 1/10000000) ≤
                (k^2 : ℝ) * Real.log ((∏ c : Fin zCells,
                  ((∑ s, zCountAt 1 c s).factorial / ∏ s, (zCountAt 1 c s).factorial) *
                  5 ^ (∑ s, zCountAt 1 c s * Boundary.ones s) : ℕ) : ℝ) +
                Real.log ((R.a * R.b * R.c : ℕ) : ℝ) := by sorry
