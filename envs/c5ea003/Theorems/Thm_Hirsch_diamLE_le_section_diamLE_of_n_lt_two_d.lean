-- Prove2me | Theorems.Thm_Hirsch_diamLE_le_section_diamLE_of_n_lt_two_d
-- name    : Hirsch.diamLE_le_section_diamLE_of_n_lt_two_d
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T14:54:33.652932+00:00
-- url     : https://prove2.me/theorems/0e4f233c-418a-4884-bbfb-dbfc7f76bc76
-- title:
--   Sub-balanced H-polyhedra inherit diameter from equality sections
-- statement:
--   Let $P\subseteq\mathbb R^d$ be an H-polyhedron defined by $n$ inequalities, with $n<2d$. Then any two vertices share a tight inequality: an extreme point is tight on at least $d$ rows (otherwise a line through it stays feasible), so two tight-row sets of size at least $d$ in a universe of size $n<2d$ cannot be disjoint. This is the complement of the spindle constraint $n\ge 2d$ for complementary tight sets.
--
--   Consequently, if every equality section $P\cap\{\langle a_i,x\rangle=b_i\}$ has padded diameter at most $B$, then so does $P$:
--
--   $$
--   \operatorname{DiamLE}(P,B).
--   $$
--
--   The walk between two vertices may be taken inside their shared equality section, whose edges remain edges of $P$. This reduces the sub-balanced regime $n<2d$ to diameter bounds on facets. It does not treat the critical balanced case $n=2d$, and it does not prove a uniform polynomial in $(n+d)$.
--
--   **Formalization Note** Boundedness and simplicity are not assumed. Tight-row cardinality at least $d$ holds for every extreme point of a finite H-presentation in $\mathbb R^d$.
-- source:
--   Complement of the spindle row-count $n\ge 2d$ (Prove2Me Hirsch.spindle_n_ge_two_d). Classical observation that $d$-subsets of a set of size $<2d$ intersect; used in Klee--Walkup reductions below the $d$-step equator $n=2d$.

import Definitions.Def_Hirsch_model
set_option autoImplicit false
open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem diamLE_le_section_diamLE_of_n_lt_two_d
    {d n B : ℕ} (hn : n < 2 * d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hF : ∀ i : Fin n,
      DiamLE (Hpoly a b ∩ {x | ⟪a i, x⟫ = b i}) B) :
    DiamLE (Hpoly a b) B := by sorry

end Hirsch
