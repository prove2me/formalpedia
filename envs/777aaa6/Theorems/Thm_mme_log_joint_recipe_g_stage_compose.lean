-- Prove2me | Theorems.Thm_mme_log_joint_recipe_g_stage_compose
-- name    : mme_log_joint_recipe_g_stage_compose
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T01:01:49.565984+00:00
-- url     : https://prove2.me/theorems/4d8ff1cc-3ad3-4532-8242-676d24376e12
-- title:
--   Bookkeeping for one stage of a graded joint recipe
-- statement:
--   This is the bookkeeping rule for one stage of a graded logarithmic joint recipe.
--
--   Let $P,Q$ be predicates on words of length $N$, and let $\ell'<\ell$ be levels. Suppose we are given the data of a stage from level $\ell$ to level $\ell'$: a partition of the $N$ positions into parts $j\in\mathrm{Fin}\,p$ of sizes $s_j$ (an equivalence $\pi:\bigsqcup_j \mathrm{Fin}\,s_j\simeq \mathrm{Fin}\,N$), part predicates $S_j,T_j$ on words of length $s_j$ such that the parts' sources $S_j$ jointly imply $P$ and $Q$ implies all targets $T_j$, part stages $D_j$ from $S_j$ to $T_j$ at level $\ell'$, and a continuation recipe $R'$ of level $\ell'$ with source $Q$. Let $X,Y\in\mathbb N$ and $\alpha,\beta\in\mathbb R$.
--
--   **Claim.** If $1\le \mathrm{types}(D_j)\le X$ for all $j$, $1\le\mathrm{inputs}(R')\le Y$, $\alpha\le\sum_j\mathrm{rate}(D_j)$ and $\beta\le\mathrm{logOutputs}(R')$, then there is a graded joint recipe $R$ of level $\ell$ with source $P$ such that
--
--   $$
--   1\le \mathrm{inputs}(R)\le X^{p}\,Y,\qquad \alpha+\beta\le \mathrm{logOutputs}(R),\qquad (R.a,R.b,R.c)=(R'.a,R'.b,R'.c).
--   $$
--
--   **Role.** This is the composition step used whenever a recipe starts with a stage: the stage contributes its summed rate and multiplies the input count by the product of its type counts, and all dimensions come from the continuation. It is used for the level-3 to level-2 stage of the hashed construction (six parts), and applies equally to the later level-2 to level-1 stage.
--
--   **Formalization Note.** $R$ is `LogJointRecipeG.stage` applied to the given data; the statement is about `LogJointRecipeG.inputs`, `.logOutputs`, `.a`, `.b`, `.c`.
-- source:
--   Prove2Me mission 7e65274f (More Asymmetry Bound: omega < 2.37134); marwahaha's plan comment of 2026-09-24 (level-3 stage with six part stages, then a level-2 continuation; WP5/WP6); rate margins 7fd711a3 and ccc30641, 832e7ff8, 72d2111a, cee956b4, e1adcbfb, 662adf75; released data of Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, arXiv 2404.16349v3.

import Definitions.Def_mme_graded_integer_regional_step_data

open BigOperators MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem mme_log_joint_recipe_g_stage_compose {N ell lower parts : ℕ} {P Q : Predicate N}
    (level_decreases : lower < ell)
    (size : Fin parts → ℕ)
    (positions : ((j : Fin parts) × Fin (size j)) ≃ Fin N)
    (S T : ∀ j, Predicate (size j))
    (source : ∀ i x, (∀ j, S j i (fun r ↦ x (positions ⟨j, r⟩))) → P i x)
    (steps : ∀ j, LogPartStageG (size j) lower (S j) (T j))
    (target : ∀ i x, Q i x → ∀ j, T j i (fun r ↦ x (positions ⟨j, r⟩)))
    (next : LogJointRecipeG N lower Q)
    (X Y : ℕ) (α β : ℝ)
    (htypes : ∀ j, 1 ≤ (steps j).types ∧ (steps j).types ≤ X)
    (hnext1 : 1 ≤ next.inputs) (hnextY : next.inputs ≤ Y)
    (hα : α ≤ ∑ j, (steps j).rate) (hβ : β ≤ next.logOutputs) :
    ∃ R : LogJointRecipeG N ell P,
      1 ≤ R.inputs ∧ R.inputs ≤ X ^ parts * Y ∧
      α + β ≤ R.logOutputs ∧
      R.a = next.a ∧ R.b = next.b ∧ R.c = next.c := by sorry
