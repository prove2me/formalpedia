-- Prove2me | Theorems.Thm_mme_released_global_graded_hashed_level3_stage_level2_continuation
-- name    : mme_released_global_graded_hashed_level3_stage_level2_continuation
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T01:01:50.412099+00:00
-- url     : https://prove2.me/theorems/88764c0e-b432-493d-a1a7-9a92be9dc2e2
-- title:
--   Hashed construction as a level-3 stage and a level-2 continuation
-- statement:
--   This is the hashed construction at a chosen reference, in the form of a level-3 stage followed by a level-2 continuation, with the rate budget split between them.
--
--   Fix the released global data, with $D=10^{12}$ and $\mathrm{blocks}(K)=D^5K$; write $n=6\,\mathrm{blocks}(k^2)$. For a scale $K$ and a family $a=(a_o)_{o\in\mathrm{Fin}\,6}$ of released global references at scale $K$, let $N_K(a)$ be the number of hashed (positive) positions, and let $\mathcal Q_K(a,e)$ be the hashed source predicate `QPos` with tolerance $e$ for all six owners.
--
--   **Claim.** For every $e$ with $0<e\le1$ there is $C\in\mathbb N$ such that for every $k_0$ there is $k\ge k_0$ with the following property. If $k>0$, then there are a reference family $a$ at scale $K=k^2$ and
--
--   - a partition of the $N_K(a)$ positions into six parts $j\in\mathrm{Fin}\,6$ of sizes $s_j$,
--   - part predicates $S_j,T_j$ on words of length $s_j$ and a predicate $Q$ on words of length $N_K(a)$, such that the six sources $S_j$ jointly imply $\mathcal Q_K(a,e)$ and $Q$ implies every target $T_j$ (each on its part's positions),
--   - graded part stages $D_j$ from $S_j$ to $T_j$ with lower level $2$,
--   - a graded logarithmic joint recipe $R'$ of level $2$ with source $Q$,
--
--   satisfying
--
--   1. $1\le\mathrm{types}(D_j)\le(k+1)^C$ for each $j$;
--   2. $n\cdot 0.7363871\le\sum_j \mathrm{rate}(D_j)$;
--   3. $1\le\mathrm{inputs}(R')\le(k+1)^C$ and $1\le R'.a\,R'.b\,R'.c$;
--   4. $n\cdot 0.5859676\le\mathrm{logOutputs}(R')$;
--   5. $n\cdot 5.83785872051\le\log(R'.a\,R'.b\,R'.c)$.
--
--   **Role.** This is the level-3/level-2 split of [the hashed construction with an explicit dimension target](p2m:theorem/a3ea7049-f313-41d0-9776-eab98b343dc2), following the plan in the mission comments: part $j$ is the band-part stage (or the square-scale tolerance stage) for orientation/region $j$, and $R'$ is the level-2 continuation (zero-half boundary, the single-type level-2 step, level-1 boundary). The stage's rate share $0.7363871$ is below $\sum_\rho c_\rho=0.73638718416$ per $n$, the sum of the six proved region rate margins $c_\rho\cdot 6\cdot10^{48}<\mathrm{regionalRate}_\rho$ (with $c_\rho\cdot10^{-12}$ per $n$). The continuation's share $0.5859676$ is below the level-2 margin $0.585967670317$ per $n$. The two shares add to exactly the required $1.3223547$. All dimensions come from the continuation, since a stage does not change dimensions.
--
--   **Formalization Note.** The parts are given by `positions : ((j : Fin 6) × Fin (size j)) ≃ Fin (partSize (k^2) a 1)`, the stages are `LogPartStageG (size j) 2 (S j) (T j)`, and the continuation is `LogJointRecipeG (partSize (k^2) a 1) 2 Q`. The degree $C$ is chosen after $e$ and before $k_0$; the reference family and all stage data are chosen after $k$.
-- source:
--   Prove2Me mission 7e65274f (More Asymmetry Bound: omega < 2.37134); marwahaha's plan comment of 2026-09-24 (level-3 stage with six part stages, then a level-2 continuation; WP5/WP6); rate margins 7fd711a3 and ccc30641, 832e7ff8, 72d2111a, cee956b4, e1adcbfb, 662adf75; released data of Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, arXiv 2404.16349v3.

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

theorem mme_released_global_graded_hashed_level3_stage_level2_continuation :
    ∀ e : ℝ, 0 < e → e ≤ 1 → ∃ C : ℕ,
      ∀ k0 : ℕ, ∃ k : ℕ, k0 ≤ k ∧
        ∀ (hk : 0 < k^2), ∃ a : ∀ o : Fin 6, Reference o (k^2),
          ∃ (size : Fin 6 → ℕ)
            (positions : ((j : Fin 6) × Fin (size j)) ≃ Fin (partSize (k^2) a 1))
            (S T : ∀ j, Predicate (size j))
            (Q : Predicate (partSize (k^2) a 1)),
            (∀ i x, (∀ j, S j i (fun r ↦ x (positions ⟨j, r⟩))) →
              QPos (k^2) a (fun _ ↦ e) i x) ∧
            (∀ i x, Q i x → ∀ j, T j i (fun r ↦ x (positions ⟨j, r⟩))) ∧
            ∃ (steps : ∀ j, LogPartStageG (size j) 2 (S j) (T j))
              (next : LogJointRecipeG (partSize (k^2) a 1) 2 Q),
              (∀ j, 1 ≤ (steps j).types ∧ (steps j).types ≤ (k + 1) ^ C) ∧
              (6 * blocks (k^2) : ℝ) * ((7363871 : ℝ)/10000000) ≤ ∑ j, (steps j).rate ∧
              1 ≤ next.inputs ∧
              next.inputs ≤ (k + 1) ^ C ∧
              1 ≤ next.a * next.b * next.c ∧
              (6 * blocks (k^2) : ℝ) * ((5859676 : ℝ)/10000000) ≤ next.logOutputs ∧
              (6 * blocks (k^2) : ℝ) * ((583785872051 : ℝ)/100000000000) ≤
                Real.log ((next.a * next.b * next.c : ℕ) : ℝ) := by sorry
