-- Prove2me | Theorems.Thm_Hirsch_ridge_visible_neighbor_of_n_eq_two_d_add_two
-- name    : Hirsch.ridge_visible_neighbor_of_n_eq_two_d_add_two
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T17:16:16.287532+00:00
-- url     : https://prove2.me/theorems/62af819f-0cc8-4ffc-b0f2-d12da54ceee9
-- title:
--   Ridge-visible neighbour in the $n\le 2d+2$ one-collision regime
-- statement:
--   Let $P\subseteq\mathbb R^d$ be a bounded simple H-polytope with $n\le 2d+2$ inequalities. Simplicity means every vertex is tight on exactly $d$ rows. Let $i$ be a describing row that is tight at two distinct vertices $z_1\neq z_2$. Then every vertex $u$ of $P$ is ridge-visible to row $i$, or is adjacent to a ridge-visible vertex.
--
--   Ridge-visible means $u$ is tight on row $i$, or tight on some other row that meets row $i$ inside $P$. The cases $n\le 2d$ (distance $0$) and $n=2d+1$ (distance at most $1$, by leave-one ray shooting) are already proved. The new layer is $n=2d+2$.
--
--   If $u$ is not ridge-visible, its $d$ tight rows are far from $i$, and $z_1,z_2$ contribute at least $d+1$ near rows. That leaves at most one leftover far inequality $H$. Every leave-one extreme ray from $u$ that misses the near rows must therefore enter this same $H$. The feasible region is then contained in the simplicial cone at $u$ cut by the halfspace of $H$, which is the simplex spanned by $u$ and its $d$ neighbours. Every generator of that simplex is strictly slack on row $i$, so every point of $P$ is strictly slack on row $i$, contradicting tightness of $z_1$.
--
--   $$
--   n\le 2d+2 \quad\Longrightarrow\quad \text{RV-distance}\le 1
--   $$
--   for simple bounded H-polytopes, on any row attained at two vertices.
--
--   This is the one-collision layer of the ridge-visible recurrence. It does not treat $n\ge 2d+3$, where two leftover far rows appear and the far polyhedron may be a product of simplices, and it does not by itself close the polynomial Hirsch conjecture.
--
--   **Formalization Note** Boundedness guarantees that each extreme ray from a simple vertex hits a new inequality in finite time. Dual-basis leave-one directions give barycentric coordinates on the simplex. The adjacent vertices are constructed by ray shooting; the segment cut by the remaining $d-1$ equalities is an edge.
-- source:
--   Campaign research on ridge-visible access for the Polynomial Hirsch conjecture (2026-09-11). Companion to Hirsch.ridge_visible_of_n_le_two_d and Hirsch.ridge_visible_neighbor_of_n_le_two_d_add_two. Novel one-collision / leftover-simplex argument at n=2d+2.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem ridge_visible_neighbor_of_n_eq_two_d_add_two
    {d n : ℕ} (hn : n ≤ 2 * d + 2)
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
