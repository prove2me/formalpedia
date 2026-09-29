-- Prove2me | Theorems.Thm_Hirsch_nonzero_supporting_row_of_distinct_extremes
-- name    : Hirsch.nonzero_supporting_row_of_distinct_extremes
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-06T12:39:56.159104+00:00
-- url     : https://prove2.me/theorems/da958d91-8db1-48eb-bb2c-5f77e1a7d136
-- title:
--   A distinct extreme point has a nonzero tight supporting row
-- statement:
--   Let $P=\{x\in\mathbb R^d:\langle a_i,xangle\le b_i\}$ be a bounded H-polytope. If $u$ and $v$ are distinct extreme points of $P$, then the target vertex $v$ lies on at least one supporting inequality whose normal is nonzero:
--
--   $$
--   \exists i,\qquad a_i
--   e0\quad	ext{and}\quad \langle a_i,vangle=b_i.
--   $$
--
--   The distinctness hypothesis excludes the zero-dimensional singleton case, where a bounded polyhedron can have no nonzero rows. This is the finite-dimensional support lemma needed before routing from $u$ to a supporting face of $v$.
--
--   **Formalization Note** The statement uses the mission’s exact `Hpoly` and `Set.extremePoints` definitions and allows redundant and zero-normal inequalities.
-- source:
--   Derived support lemma for the target-face-access decomposition of the Polynomial Hirsch Conjecture; context Kalai, The polynomial Hirsch conjecture (Polymath 3), 2010, and Santos, TOP 21 (2013), arXiv:1307.5900, Conjecture 1.1.

import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem nonzero_supporting_row_of_distinct_extremes :
    ∀ (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      ∀ u ∈ Set.extremePoints ℝ (Hpoly a b),
      ∀ v ∈ Set.extremePoints ℝ (Hpoly a b), u ≠ v →
      ∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, v⟫ = b i := by sorry

end Hirsch
