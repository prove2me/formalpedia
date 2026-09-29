-- Prove2me | Theorems.Thm_mme_released_global_graded_hashed_construction_some_reference_hashed_dims
-- name    : mme_released_global_graded_hashed_construction_some_reference_hashed_dims
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T00:52:30.340987+00:00
-- url     : https://prove2.me/theorems/a3ea7049-f313-41d0-9776-eab98b343dc2
-- title:
--   Hashed construction at a chosen reference with an explicit dimension target
-- statement:
--   This is the hashed construction at a chosen reference, with the boundary constant $\log B$ removed from the dimension bound.
--
--   Fix the released global data, with $D=10^{12}$ and $\mathrm{blocks}(K)=D^5K$. For a scale $K$ and a family $a=(a_o)_{o\in\mathrm{Fin}\,6}$ of released global references at scale $K$, let $N_K(a)=\mathrm{partSize}(K,a,1)$ be the number of hashed (positive) positions, and let $\mathcal Q_K(a,e)$ be the hashed source predicate `QPos` with tolerance $e$ for all six owners.
--
--   **Claim.** For every $e$ with $0<e\le1$ there is a degree $C\in\mathbb N$ such that for every $k_0$ there is $k\ge k_0$ with the following property. If $k>0$, then there are a reference family $a$ at scale $K=k^2$ and a graded logarithmic joint recipe $R$ of level $3$ on $N_K(a)$ positions with source $\mathcal Q_K(a,e)$ such that:
--
--   1. $1\le \mathrm{inputs}(R)\le (k+1)^C$;
--   2. $1\le R.a\,R.b\,R.c$;
--   3. the rate bound holds:
--   $$
--   6\,\mathrm{blocks}(k^2)\cdot 1.3223547\ \le\ \mathrm{logOutputs}(R);
--   $$
--   4. the recipe's own dimensions satisfy
--   $$
--   6\,\mathrm{blocks}(k^2)\cdot 5.83785872051\ \le\ \log(R.a\,R.b\,R.c).
--   $$
--
--   **Role.** The constant is $5.83785872051=3\cdot2.09612367517-10^{-7}-0.450512205$. The [construction at a chosen reference](p2m:theorem/71693563-1700-4744-b3a2-7f624e7357ee) asks for $6\,\mathrm{blocks}(k^2)(3\cdot2.09612367517-10^{-7})\le k^2\log B+\log(R.a\,R.b\,R.c)$, where $B$ is the unit-scale boundary factor. Since $\log B\ge 6D^5\cdot0.450512205$ ([the boundary certificate](p2m:theorem/1e6f06b7-d9ba-4462-af69-0d03251d1f30)) and $k^2\cdot 6D^5=6\,\mathrm{blocks}(k^2)$, this statement implies that one. The hashed part now carries a plain per-position target: $\log(abc)/n\ge5.83785872051$ with $n=6\,\mathrm{blocks}(k^2)$. The exact value is $\log B/n=0.45051220582308\ldots$, so the rounding costs about $8\cdot10^{-10}$ per $n$, which is less than $1\%$ of the planned $10^{-7}$ dimension slack. The rate, input and source clauses are unchanged.
--
--   **Formalization Note.** The recipe type is `LogJointRecipeG (partSize (k^2) a 1) 3 (QPos (k^2) a (fun _ ↦ e))`. The degree $C$ is chosen after $e$ and before $k_0$, and the reference family $a$ is chosen after $k$.
-- source:
--   Prove2Me mission 7e65274f (More Asymmetry Bound: omega < 2.37134); marwahaha's plan comment of 2026-09-24 (WP7 dimension certificate: level-3 zero cells); boundary factor B as in theorem 71693563-1700-4744-b3a2-7f624e7357ee and 8a1dbc6c-de97-4a8b-b66f-e831372553f2; released data of Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, arXiv 2404.16349v3.

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

theorem mme_released_global_graded_hashed_construction_some_reference_hashed_dims :
    ∀ e : ℝ, 0 < e → e ≤ 1 → ∃ C : ℕ,
      ∀ k0 : ℕ, ∃ k : ℕ, k0 ≤ k ∧
        ∀ (hk : 0 < k^2), ∃ a : ∀ o : Fin 6, Reference o (k^2),
          ∃ R : LogJointRecipeG (partSize (k^2) a 1) 3 (QPos (k^2) a (fun _ ↦ e)),
            1 ≤ R.inputs ∧
            R.inputs ≤ (k + 1) ^ C ∧
            1 ≤ R.a * R.b * R.c ∧
            (6 * blocks (k^2) : ℝ) * ((13223547 : ℝ)/10000000) ≤ R.logOutputs ∧
            (6 * blocks (k^2) : ℝ) * ((583785872051 : ℝ)/100000000000) ≤
              Real.log ((R.a * R.b * R.c : ℕ) : ℝ) := by sorry
