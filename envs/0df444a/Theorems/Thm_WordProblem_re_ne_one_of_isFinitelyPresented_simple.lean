-- Prove2me | Theorems.Thm_WordProblem_re_ne_one_of_isFinitelyPresented_simple
-- name    : WordProblem.re_ne_one_of_isFinitelyPresented_simple
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-12T15:41:24.995768+00:00
-- url     : https://prove2.me/theorems/505d89c3-8fde-43a8-98fc-9ae837529f95
-- title:
--   Simplicity makes the word problem's complement semi-decidable
-- statement:
--   Let $H$ be a finitely presented *simple* group and $p = (p_1, \dots, p_n)$ a finite generating tuple. The predicate "the word $w$ over $p_1^{\pm1}, \dots, p_n^{\pm1}$ does *not* evaluate to the identity of $H$" is recursively enumerable.
--
--   $$
--   \mathrm{REPred}\big(\lambda\, w.\ \mathrm{evalWord}(p, w) \ne 1\big).
--   $$
--
--   If the element $x = \mathrm{evalWord}(p, w)$ is not the identity, then its normal closure $\langle\langle x \rangle\rangle$ is a nontrivial normal subgroup of the simple group $H$, hence all of $H$; in particular every generator $p_i$ is then exhibited, for some finite $k_i$, as a product of $k_i$ conjugates of $x^{\pm1}$. Conversely if $x = 1$ no such certificate exists for any generator whose normal closure would need to be nontrivial. Enumerating, for increasing bounds, all finite sequences of conjugating elements (themselves free-group words) and checking via the ordinary word-equality semi-decision procedure (available since $H$ is finitely presented) whether the resulting product equals each $p_i$ gives the semi-decision procedure for $x \ne 1$.
--
--   Combined with the (simplicity-free) semi-decidability of $x = 1$, Post's theorem gives decidability of the word problem of a finitely presented simple group with respect to any of its finite generating tuples — the classical fact behind the easy direction of the Boone–Higman characterization.
--
--   **Formalization Note** `Word`, `evalWord` and `REPred` are the existing notions from this mission's definitions bundle and from Mathlib.
-- source:
--   Folklore fact in combinatorial group theory, discussed around the original statement of the Boone–Higman conjecture in W. W. Boone and G. Higman, An algebraic characterization of groups with soluble word problem, J. Austral. Math. Soc. 18 (1974), https://doi.org/10.1017/S1446788700019108: that a finitely presented group's word problem is semi-decidable, that simplicity makes the complement semi-decidable too, and that semi-decidability of the word problem does not depend on the choice of finite generating tuple.

import Mathlib
import Definitions.Def_BooneHigman

open OAI.FiniteAlgebraicEnvelopes

namespace WordProblem

universe u

theorem re_ne_one_of_isFinitelyPresented_simple {H : Type u} [Group H]
    [Group.IsFinitelyPresented H] [IsSimpleGroup H]
    {n : ℕ} (p : Fin n → H) (hp : Subgroup.closure (Set.range p) = ⊤) :
    REPred (fun word : Word n => evalWord p word ≠ 1) := by
  sorry

end WordProblem
