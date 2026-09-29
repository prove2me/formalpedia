-- Prove2me | Theorems.Thm_mme_released_global_graded_hashed_recursive_construction_scalar_cap
-- name    : mme_released_global_graded_hashed_recursive_construction_scalar_cap
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T21:26:20.346591+00:00
-- url     : https://prove2.me/theorems/879cd4b1-a08d-4b0a-bac3-dcde66d168d3
-- title:
--   Scalar-tolerance graded construction on the hashed part
-- statement:
--   This is the scalar-tolerance form of the fixed-cap graded construction on the hashed part of the released global candidate.
--
--   For every scalar tolerance $0<e\le 1$ and every $k_0$, there is a scale $k\ge k_0$ with the following property. For every admissible reference arrangement $a$ at squared scale $k^2$, there is a level-three graded logarithmic joint recipe $R$ on the hashed part whose source predicate is $\mathrm{QPos}(k^2,a,e)$. This predicate says that every hashed block has its cell's grades and that each owner's cell histograms lie within $e$ of the released profile, with the same tolerance $e$ for all six owners. The recipe satisfies exactly the input, weighted-dimension, output-rate and dimension-rate bounds of the parent statement `mme_released_global_graded_hashed_recursive_construction_caps_one`:
--
--   $$6\,\mathrm{blocks}(k^2)\cdot 1.3223546+\log\operatorname{inputs}(R)\le \operatorname{logOutputs}(R),$$
--
--   $$6\,\mathrm{blocks}(k^2)\cdot\bigl(3\cdot 2.09612367517-10^{-7}\bigr)\le \log\Bigl(Z_k\cdot R.a\,R.b\,R.c\Bigr),$$
--
--   where $Z_k$ is the explicit multinomial-times-$5^{\text{ones}}$ dimension factor of the boundary blocks.
--
--   Because $\mathrm{QPos}$ is monotone in the tolerance profile, a recipe for the scalar tolerance $e=\min_o \varepsilon_o$ transfers to any owner-wise profile $\varepsilon$ with all $\varepsilon_o \le 1$. Only the scalar case therefore needs to be constructed.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 5-7 (recursive hashing, Theorem 5.3/6.4) and Section 7 released fourth-power parameters; scalar-tolerance form of Prove2Me theorem mme_released_global_graded_hashed_recursive_construction_caps_one (b4f708f1-b8d2-4ac8-a8b2-7c5e2c584426).

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

theorem mme_released_global_graded_hashed_recursive_construction_scalar_cap :
    ∀ e : ℝ, 0 < e → e ≤ 1 →
      ∀ k0 : ℕ, ∃ k : ℕ, k0 ≤ k ∧
        ∀ (hk : 0 < k^2) (a : ∀ o : Fin 6, Reference o (k^2)),
          ∃ R : LogJointRecipeG (partSize (k^2) a 1) 3 (QPos (k^2) a (fun _ ↦ e)),
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
