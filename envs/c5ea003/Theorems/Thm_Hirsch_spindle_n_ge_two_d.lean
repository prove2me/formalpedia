-- Prove2me | Theorems.Thm_Hirsch_spindle_n_ge_two_d
-- name    : Hirsch.spindle_n_ge_two_d
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-05T14:21:01.689674+00:00
-- url     : https://prove2.me/theorems/143c07df-fbd0-4443-a5f2-82b4e703f48b
-- title:
--   A $d$-spindle has at least $2d$ inequalities
-- statement:
--   A spindle in dimension $d$ cannot be described by fewer than $2d$ inequalities.
--
--   Let $P\subseteq\mathbb R^d$ be an H-polytope cut out by $n$ inequalities, and let $u,v$ be extreme points of $P$ such that every describing inequality is tight at exactly one of $u$ or $v$. If $d>0$, then
--
--   $$
--   n\ge 2d.
--   $$
--
--   The two tight sets are disjoint by the spindle (XOR) hypothesis. Each extreme point of a $d$-dimensional polytope is the unique solution of at least $d$ linearly independent tight inequalities (otherwise a line through the point would remain in $P$), so each tight set has cardinality at least $d$.
--
--   This is the observation that the asimpliciality $s=n-2d$ of a spindle is nonnegative, used as the induction parameter in Santos' strong $d$-step theorem.
--
--   **Formalization Note.** The H-polytope may include redundant inequalities; the bound counts all describing inequalities, so it remains valid in the presence of redundancy.
-- source:
--   F. Santos, A counterexample to the Hirsch conjecture, Annals of Mathematics 176 (2012) 383-412, https://arxiv.org/abs/1006.2814, Definition 1.4 and the induction on $s=n-2d$ in Theorem 2.6 (base $s=0$ requires $n\ge 2d$).

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem spindle_n_ge_two_d (d n : ℕ) (hd : 0 < d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (hspindle : ∀ i, (⟪a i, u⟫ = b i) ↔ ⟪a i, v⟫ ≠ b i) :
    2 * d ≤ n := by sorry

end Hirsch
