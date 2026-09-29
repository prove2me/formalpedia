-- Prove2me | Theorems.Thm_mme_released_global_graded_hashed_construction_poly_inputs_some_reference
-- name    : mme_released_global_graded_hashed_construction_poly_inputs_some_reference
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T00:12:13.840876+00:00
-- url     : https://prove2.me/theorems/71693563-1700-4744-b3a2-7f624e7357ee
-- title:
--   Hashed graded construction with a polynomial input count, at a chosen reference
-- statement:
--   This is the hashed graded construction with a polynomial input count, where the construction may choose the released reference family.
--
--   Fix the released global data. For a scale $K$ and a family $a=(a_o)_{o\in\mathrm{Fin}\,6}$ of released global references at scale $K$, let $N_K(a)=\mathrm{partSize}(K,a,1)$ be the number of hashed (positive) block positions. Let $\mathcal Q_K(a,e)$ be the hashed source predicate `QPos` with the same tolerance $e$ for all six owners. Write $\mathrm{blocks}(K)=D^5K$ with $D=10^{12}$. Let
--
--   $$
--   B=\prod_{c\ \text{zero cell}}\binom{\sum_s z_1(c,s)}{(z_1(c,s))_s}\,5^{\sum_s z_1(c,s)\,\mathrm{ones}(s)}
--   $$
--
--   be the unit-scale boundary dimension factor.
--
--   **Claim.** For every $e$ with $0<e\le1$ there is a degree $C\in\mathbb N$ such that for every $k_0$ there is $k\ge k_0$ with the following property. If $k>0$, then **there exist** a reference family $a$ at scale $K=k^2$ and a graded logarithmic joint recipe $R$ of level $3$ on $N_K(a)$ positions with source $\mathcal Q_K(a,e)$ such that:
--
--   1. $1\le \mathrm{inputs}(R)\le (k+1)^C$;
--   2. $1\le R.a\,R.b\,R.c$;
--   3. the rate bound holds:
--   $$
--   6\,\mathrm{blocks}(k^2)\cdot 1.3223547\ \le\ \mathrm{logOutputs}(R);
--   $$
--   4. the dimension bound holds:
--   $$
--   6\,\mathrm{blocks}(k^2)\,\bigl(3\cdot 2.09612367517-10^{-7}\bigr)\ \le\ k^2\log B+\log(R.a\,R.b\,R.c).
--   $$
--
--   **Role.** This is [the polynomial-input hashed construction](p2m:theorem/69b84798-206c-4f65-b1a1-2167ff28044f) with the universal quantifier over reference families replaced by an existential one. The two are equivalent. References exist at every scale, and [reference transport](p2m:theorem/3fd55e04-bd4f-4de5-800b-082bb194c083) moves a recipe from one reference family to any other without changing inputs, output rate or dimensions. The construction may therefore choose its own block layout, for example the blocks of each owner sorted by cell, which fixes the positions used by the level-3 stage.
--
--   **Formalization Note.** The recipe type is `LogJointRecipeG (partSize (k^2) a 1) 3 (QPos (k^2) a (fun _ ↦ e))`. The degree $C$ is chosen after $e$ and before $k_0$. The reference family $a$ is chosen after $k$.
-- source:
--   Prove2Me mission 7e65274f (More Asymmetry Bound: omega < 2.37134); structural reduction of theorem 69b84798-206c-4f65-b1a1-2167ff28044f via the released reference definition (Def_mme_released_global_frame_data: Reference o k has exact cell counts k*coarseCounts o).

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

theorem mme_released_global_graded_hashed_construction_poly_inputs_some_reference :
    ∀ e : ℝ, 0 < e → e ≤ 1 → ∃ C : ℕ,
      ∀ k0 : ℕ, ∃ k : ℕ, k0 ≤ k ∧
        ∀ (hk : 0 < k^2), ∃ a : ∀ o : Fin 6, Reference o (k^2),
          ∃ R : LogJointRecipeG (partSize (k^2) a 1) 3 (QPos (k^2) a (fun _ ↦ e)),
            1 ≤ R.inputs ∧
            R.inputs ≤ (k + 1) ^ C ∧
            1 ≤ R.a * R.b * R.c ∧
            (6 * blocks (k^2) : ℝ) * ((13223547 : ℝ)/10000000) ≤ R.logOutputs ∧
            (6 * blocks (k^2) : ℝ) *
              (3 * ((209612367517 : ℝ)/100000000000) - 1/10000000) ≤
                (k^2 : ℝ) * Real.log ((∏ c : Fin zCells,
                  ((∑ s, zCountAt 1 c s).factorial / ∏ s, (zCountAt 1 c s).factorial) *
                  5 ^ (∑ s, zCountAt 1 c s * Boundary.ones s) : ℕ) : ℝ) +
                Real.log ((R.a * R.b * R.c : ℕ) : ℝ) := by sorry
