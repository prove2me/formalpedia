-- Prove2me | Theorems.Thm_mme_released_global_graded_hashed_recursive_construction_scalar_cap_hashed_poly_inputs
-- name    : mme_released_global_graded_hashed_recursive_construction_scalar_cap_hashed_poly_inputs
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T23:04:37.099432+00:00
-- url     : https://prove2.me/theorems/69b84798-206c-4f65-b1a1-2167ff28044f
-- title:
--   Hashed graded construction with a polynomial input count
-- statement:
--   This is the hashed graded construction at scalar tolerance, with the input count separated into a polynomial bound.
--
--   Fix the released global data. For a scale $K$ and a family $a=(a_o)_{o\in\mathrm{Fin}\,6}$ of released global references at scale $K$, let $N_K(a)=\mathrm{partSize}(K,a,1)$ be the number of hashed (positive) block positions. Let $\mathcal Q_K(a,e)$ be the hashed source predicate `QPos` with the same tolerance $e$ for all six owners. Write $\mathrm{blocks}(K)=D^5K$ with $D=10^{12}$. Let
--
--   $$
--   B=\prod_{c\ \text{zero cell}}\binom{\sum_s z_1(c,s)}{(z_1(c,s))_s}\,5^{\sum_s z_1(c,s)\,\mathrm{ones}(s)}
--   $$
--
--   be the unit-scale boundary dimension factor.
--
--   **Claim.** For every $e$ with $0<e\le1$ there is a degree $C\in\mathbb N$ such that for every $k_0$ there is $k\ge k_0$ with the following property. If $k>0$, then for every reference family $a$ at scale $K=k^2$ there is a graded logarithmic joint recipe $R$ of level $3$ on $N_K(a)$ positions with source $\mathcal Q_K(a,e)$ such that:
--
--   1. $1\le \mathrm{inputs}(R)\le (k+1)^C$;
--   2. $1\le R.a\,R.b\,R.c$;
--   3. the rate bound holds, with no input-count term:
--   $$
--   6\,\mathrm{blocks}(k^2)\cdot 1.3223547\ \le\ \mathrm{logOutputs}(R);
--   $$
--   4. the dimension bound holds:
--   $$
--   6\,\mathrm{blocks}(k^2)\,\bigl(3\cdot 2.09612367517-10^{-7}\bigr)\ \le\ k^2\log B+\log(R.a\,R.b\,R.c).
--   $$
--
--   **Role.** This separates the polynomial type-count loss from [the hashed construction](p2m:theorem/5f83bcf1-af4e-41da-89a4-510ec5a0eea4). The type count only needs a polynomial bound in $k$ whose degree may depend on $e$. In exchange, the rate constant rises from $1.3223546$ to $1.3223547$, which is still below the planned budget $\sum_\rho c_\rho+c_2=1.3223548545$. The extra $10^{-7}$ per $6\,\mathrm{blocks}(k^2)$, namely $6\cdot10^{53}k^2$, absorbs $\log\mathrm{inputs}\le C\log(k+1)$ once $k\ge C$. The level-3 six-part stage and the level-2 continuation contribute polynomially many types, so their counts fit this form.
--
--   **Formalization Note.** The recipe type is `LogJointRecipeG (partSize (k^2) a 1) 3 (QPos (k^2) a (fun _ ↦ e))`. The degree $C$ is chosen after $e$ and before $k_0$, so it may depend on $e$ but on nothing else.
-- source:
--   Prove2Me mission 7e65274f (More Asymmetry Bound: omega < 2.37134); marwahaha's plan comment of 2026-09-24 (rate budget 1.3223548545 vs 1.3223546, log inputs = O(log t)); strengthening of theorem 5f83bcf1-af4e-41da-89a4-510ec5a0eea4.

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

theorem mme_released_global_graded_hashed_recursive_construction_scalar_cap_hashed_poly_inputs :
    ∀ e : ℝ, 0 < e → e ≤ 1 → ∃ C : ℕ,
      ∀ k0 : ℕ, ∃ k : ℕ, k0 ≤ k ∧
        ∀ (hk : 0 < k^2) (a : ∀ o : Fin 6, Reference o (k^2)),
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
