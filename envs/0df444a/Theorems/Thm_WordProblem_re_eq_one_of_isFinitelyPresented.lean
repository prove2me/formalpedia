-- Prove2me | Theorems.Thm_WordProblem_re_eq_one_of_isFinitelyPresented
-- name    : WordProblem.re_eq_one_of_isFinitelyPresented
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-12T15:41:37.621059+00:00
-- url     : https://prove2.me/theorems/c1334489-b08e-4e43-ae27-2fb541fcb09b
-- title:
--   The word problem of a finitely presented group is semi-decidable
-- statement:
--   Let $H$ be a finitely presented group and $p = (p_1, \dots, p_n)$ a finite tuple of elements of $H$ that generates $H$. The predicate "the word $w$ over $p_1^{\pm1}, \dots, p_n^{\pm1}$ evaluates to the identity of $H$" is recursively enumerable.
--
--   $$
--   \mathrm{REPred}\big(\lambda\, w.\ \mathrm{evalWord}(p, w) = 1\big).
--   $$
--
--   Since $H$ is finitely presented, say as the quotient of a free group on finitely many generators by the normal closure of a finite relator set, membership of a free-group word in that normal closure is witnessed by a finite sequence of conjugates of the relators (and their inverses) whose product equals the word; enumerating all such finite sequences gives a semi-decision procedure for "$w = 1$ in $H$", for the word written over *any* finite generating tuple (by first substituting a representative free-group word for each generator of the tuple).
--
--   This is the half of the classical argument for the decidability of the word problem of a finitely presented simple group that needs no simplicity hypothesis; it is the r.e. side of Post's theorem (semi-decidable + co-semi-decidable implies decidable), which supplies the other side.
--
--   **Formalization Note** `Word`, `evalWord` and `REPred`/`ComputablePred` are Mathlib's and this mission's existing notions; no new definitions are introduced.
-- source:
--   Folklore fact in combinatorial group theory, discussed around the original statement of the Boone–Higman conjecture in W. W. Boone and G. Higman, An algebraic characterization of groups with soluble word problem, J. Austral. Math. Soc. 18 (1974), https://doi.org/10.1017/S1446788700019108: that a finitely presented group's word problem is semi-decidable, that simplicity makes the complement semi-decidable too, and that semi-decidability of the word problem does not depend on the choice of finite generating tuple.

import Mathlib
import Definitions.Def_BooneHigman

open OAI.FiniteAlgebraicEnvelopes

namespace WordProblem

universe u

theorem re_eq_one_of_isFinitelyPresented {H : Type u} [Group H] [Group.IsFinitelyPresented H]
    {n : ℕ} (p : Fin n → H) (hp : Subgroup.closure (Set.range p) = ⊤) :
    REPred (fun word : Word n => evalWord p word = 1) := by
  sorry

end WordProblem
