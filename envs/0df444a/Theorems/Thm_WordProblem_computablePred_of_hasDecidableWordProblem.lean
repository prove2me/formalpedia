-- Prove2me | Theorems.Thm_WordProblem_computablePred_of_hasDecidableWordProblem
-- name    : WordProblem.computablePred_of_hasDecidableWordProblem
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-12T15:41:18.322061+00:00
-- url     : https://prove2.me/theorems/79558a24-c943-4b55-b73a-acd466b16275
-- title:
--   Decidable word problem transfers to any finite tuple
-- statement:
--   If a group $H$ has decidable word problem (`HasDecidableWordProblem H`, witnessed by some finite generating tuple), then for *any* finite tuple $h = (h_1, \dots, h_m)$ of elements of $H$ — not necessarily a generating one, and not necessarily the tuple witnessing the hypothesis — the predicate "the word $w$ over $h_1^{\pm1}, \dots, h_m^{\pm1}$ evaluates to the identity of $H$" is a computable predicate.
--
--   $$
--   \mathrm{ComputablePred}\big(\lambda\, w.\ \mathrm{evalWord}(h, w) = 1\big).
--   $$
--
--   Each $h_i$ is some (not necessarily effectively known) word over the generating tuple witnessing `HasDecidableWordProblem H`, since that tuple generates $H$; substituting those representative words for the letters of $w$ turns the question "does $w$ evaluate to $1$ over $h$" into the same question over the known decidable tuple, so a decision procedure for the latter yields one for the former. This is the standard fact that decidability of the word problem does not depend on which finite generating tuple is used, extended to an arbitrary (non-generating) finite tuple of group elements.
--
--   **Formalization Note** `HasDecidableWordProblem`, `Word`, `evalWord` and `ComputablePred` are this mission's and Mathlib's existing notions. This theorem is the bridge that lets a subgroup inherit decidability of the word problem from an ambient group it embeds into, using the *images* of the subgroup's own generators as the tuple $h$.
-- source:
--   Folklore fact in combinatorial group theory, discussed around the original statement of the Boone–Higman conjecture in W. W. Boone and G. Higman, An algebraic characterization of groups with soluble word problem, J. Austral. Math. Soc. 18 (1974), https://doi.org/10.1017/S1446788700019108: that a finitely presented group's word problem is semi-decidable, that simplicity makes the complement semi-decidable too, and that semi-decidability of the word problem does not depend on the choice of finite generating tuple.

import Mathlib
import Definitions.Def_BooneHigman

open OAI.FiniteAlgebraicEnvelopes

namespace WordProblem

universe u

theorem computablePred_of_hasDecidableWordProblem {H : Type u} [Group H]
    (hH : HasDecidableWordProblem H) {m : ℕ} (h : Fin m → H) :
    ComputablePred (fun word : Word m => evalWord h word = 1) := by
  sorry

end WordProblem
