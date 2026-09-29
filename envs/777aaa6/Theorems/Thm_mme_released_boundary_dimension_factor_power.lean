-- Prove2me | Theorems.Thm_mme_released_boundary_dimension_factor_power
-- name    : mme_released_boundary_dimension_factor_power
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T22:51:39.535266+00:00
-- url     : https://prove2.me/theorems/8a1dbc6c-de97-4a8b-b66f-e831372553f2
-- title:
--   The boundary dimension factor dominates the k-th power of its unit-scale value
-- statement:
--   Consider the boundary blocks of the released global candidate, the blocks whose cell has a zero grade in some mode. For a boundary cell $c$ at scale $k$, let $n^{(k)}_{c,s}$ be its released histogram over level-three words $s$ (`zCountAt k c s`), and let $\mathrm{ones}(s)$ count the letters $1$ in $s$. These cells contribute the exact matrix-dimension factor
--
--   $$Z_k(a)=\prod_{c}\binom{N_c^{(k)}}{(n^{(k)}_{c,s})_s}\,5^{\sum_s n^{(k)}_{c,s}\,\mathrm{ones}(s)},$$
--
--   where $N^{(k)}_c$ is the number of boundary blocks of the arrangement $a$ lying in cell $c$. Let
--
--   $$B=\prod_{c}\binom{\sum_s n^{(1)}_{c,s}}{(n^{(1)}_{c,s})_s}\,5^{\sum_s n^{(1)}_{c,s}\,\mathrm{ones}(s)}$$
--
--   be the corresponding factor at unit scale. This is an explicit natural number that does not depend on any arrangement.
--
--   **Theorem.** For every $k>0$ and every admissible arrangement $a$ at scale $k$,
--
--   $$1\le B\qquad\text{and}\qquad B^{k}\le Z_k(a).$$
--
--   The factor $Z_k(a)$ does not depend on $a$, because every cell holds exactly $N^{(k)}_c=\sum_s n^{(k)}_{c,s}$ blocks, and all histograms scale linearly: $n^{(k)}_{c,s}=k\,n^{(1)}_{c,s}$. The inequality is then supermultiplicativity of multinomial coefficients, $\binom{kN}{(kn_s)}\ge\binom{N}{(n_s)}^k$. It lets the boundary dimension budget of the hashed construction be charged at the fixed rate $\log B$ per unit of scale.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 5-7; dimension accounting of the boundary (zero-cell) blocks for the released fourth-power parameters (Section 7).

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

theorem mme_released_boundary_dimension_factor_power (k : ℕ) (hk : 0 < k)
    (a : ∀ o : Fin 6, Reference o k) :
    1 ≤ (∏ c : Fin zCells,
          ((∑ s, zCountAt 1 c s).factorial / ∏ s, (zCountAt 1 c s).factorial) *
          5 ^ (∑ s, zCountAt 1 c s * Boundary.ones s)) ∧
    (∏ c : Fin zCells,
          ((∑ s, zCountAt 1 c s).factorial / ∏ s, (zCountAt 1 c s).factorial) *
          5 ^ (∑ s, zCountAt 1 c s * Boundary.ones s)) ^ k ≤
      ∏ c : Fin zCells,
          ((Fintype.card {p : Fin (zCount k a) // zCellOf k a p = c}).factorial /
            ∏ s, (zCountAt k c s).factorial) *
          5 ^ (∑ s, zCountAt k c s * Boundary.ones s) := by sorry
