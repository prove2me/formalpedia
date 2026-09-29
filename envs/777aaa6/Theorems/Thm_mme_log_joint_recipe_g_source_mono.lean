-- Prove2me | Theorems.Thm_mme_log_joint_recipe_g_source_mono
-- name    : mme_log_joint_recipe_g_source_mono
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T21:26:18.765694+00:00
-- url     : https://prove2.me/theorems/c8d0b3fe-3bbf-46b5-9ad4-61394081f6be
-- title:
--   Graded joint recipes are monotone in the source predicate
-- statement:
--   Let $R$ be a graded logarithmic joint recipe (`LogJointRecipeG`) on $N$ fine positions at level $\ell$ whose source predicate is $P$. If $P'$ is any predicate with $P \subseteq P'$, that is, $P_i(x)\Rightarrow P'_i(x)$ for every mode $i$ and every fine word $x$, then there is a recipe $R'$ with source predicate $P'$ and the same bookkeeping:
--
--   $$\operatorname{inputs}(R')=\operatorname{inputs}(R),\qquad \operatorname{logOutputs}(R')=\operatorname{logOutputs}(R),\qquad \dim(R')=\dim(R).$$
--
--   In words, weakening the source constraint never costs anything. The source predicate is used only in the `source`/`inside` containment conditions of the outermost stage, partition, boundary end, or integer step; every rate, type count and matrix dimension is unchanged. Rotations and swaps reindex the predicate by a permutation of the three modes, so the weakened predicate is pulled back along the same permutation.
-- source:
--   Structural lemma about the platform definition LogJointRecipeG (Definitions.Def_mme_graded_integer_regional_step_data), used for tolerance bookkeeping in More Asymmetry, arXiv:2404.16349v2, Section 7.

import Definitions.Def_mme_graded_integer_regional_step_data

open BigOperators MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem mme_log_joint_recipe_g_source_mono {N ell : ℕ} {P : Predicate N}
    (R : LogJointRecipeG N ell P) (P' : Predicate N) (h : ∀ i x, P i x → P' i x) :
    ∃ R' : LogJointRecipeG N ell P',
      R'.inputs = R.inputs ∧ R'.logOutputs = R.logOutputs ∧ R'.dims = R.dims := by sorry
