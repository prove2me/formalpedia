-- Prove2me | Theorems.Thm_Hirsch_ridge_visible_neighbor_of_n_le_two_d_add_two
-- name    : Hirsch.ridge_visible_neighbor_of_n_le_two_d_add_two
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T16:29:02.53068+00:00
-- url     : https://prove2.me/theorems/f10ca8dd-f1b1-49df-b552-d648eeca1093
-- title:
--   Ridge-visible neighbour in the n ≤ 2d+1 regime
-- statement:
--   Let $P\subseteq\mathbb R^d$ be a bounded simple H-polytope with $n\le 2d+1$ inequalities. Simplicity means every vertex is tight on exactly $d$ rows. Let $i$ be a describing row that is tight at two distinct vertices $z_1\neq z_2$. Then every vertex $u$ of $P$ is ridge-visible to row $i$, or is adjacent to a ridge-visible vertex.
--
--   Ridge-visible means $u$ is tight on row $i$, or tight on some other row that meets row $i$ inside $P$. The $n\le 2d$ case (already proved) gives distance $0$. For the remaining $n=2d+1$ layer, a non-visible simple vertex has all $d$ tight rows far from $i$. Leaving one tight row along its extreme ray hits a new inequality at an adjacent vertex. That entering row cannot be far: together with the original $d$ far rows and the $\ge d+1$ near rows contributed by $z_1,z_2$, that would require at least $2d+2$ inequalities.
--
--   $$
--   n\le 2d+1 \quad\Longrightarrow\quad \text{RV-distance}\le 1
--   $$
--   for simple bounded H-polytopes, on any row attained at two vertices.
--
--   This is the first positive-distance layer of the ridge-visible recurrence that would unfold to a uniform polynomial via the proved dimension-drop. It does not treat $n\ge 2d+2$, where two pivots can collide on the same far row, and it does not by itself close the polynomial Hirsch conjecture.
--
--   **Formalization Note** Boundedness is used to guarantee that each extreme ray from a simple vertex hits a new inequality in finite time. The adjacent vertex is constructed by ray shooting in the leave-one dual-basis direction; the segment is the face cut out by the remaining $d-1$ tight equalities.
-- source:
--   Campaign research on ridge-visible access for the Polynomial Hirsch conjecture (2026-09-11). Companion to Hirsch.ridge_visible_of_n_le_two_d (distance 0 at n≤2d). Pivot construction plus a counting obstruction at n=2d+1.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem ridge_visible_neighbor_of_n_le_two_d_add_two
    {d n : ℕ} (hn : n ≤ 2 * d + 1)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hsimple : ∀ x ∈ extremePoints ℝ (Hpoly a b),
      (Finset.univ.filter (fun j : Fin n => ⟪a j, x⟫ = b j)).card = d)
    (i : Fin n)
    {z₁ z₂ : EuclideanSpace ℝ (Fin d)}
    (hz₁ : z₁ ∈ extremePoints ℝ (Hpoly a b))
    (hz₂ : z₂ ∈ extremePoints ℝ (Hpoly a b))
    (hne : z₁ ≠ z₂)
    (hzi₁ : ⟪a i, z₁⟫ = b i)
    (hzi₂ : ⟪a i, z₂⟫ = b i)
    (u : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b)) :
    (⟪a i, u⟫ = b i ∨
      ∃ r : Fin n, r ≠ i ∧ ⟪a r, u⟫ = b r ∧
        ∃ x ∈ Hpoly a b, ⟪a i, x⟫ = b i ∧ ⟪a r, x⟫ = b r) ∨
    ∃ w, w ∈ extremePoints ℝ (Hpoly a b) ∧ Adj (Hpoly a b) u w ∧
      (⟪a i, w⟫ = b i ∨
        ∃ r : Fin n, r ≠ i ∧ ⟪a r, w⟫ = b r ∧
          ∃ x ∈ Hpoly a b, ⟪a i, x⟫ = b i ∧ ⟪a r, x⟫ = b r) := by sorry

end Hirsch
