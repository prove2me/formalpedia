-- Prove2me | Theorems.Thm_Hirsch_ridge_visible_neighbor_of_n_le_two_d_add_four
-- name    : Hirsch.ridge_visible_neighbor_of_n_le_two_d_add_four
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T23:20:38.967129+00:00
-- url     : https://prove2.me/theorems/aad0365e-3da1-4a26-8bee-0c037b3992f0
-- title:
--   Ridge-visible access in the $n\le 2d+4$ three-leftover regime
-- statement:
--   Let $P\subseteq\mathbb R^d$ be a bounded simple H-polytope with $n\le 2d+4$ inequalities. Simplicity means every vertex is tight on exactly $d$ rows. Let $i$ be a describing row that is tight at two distinct vertices $z_1\neq z_2$. Then every vertex $u$ of $P$ reaches the ridge-visible set of row $i$ by a stay-or-adjacent walk of length $K=n-2d\le 4$.
--
--   Ridge-visible means $u$ is tight on row $i$, or tight on some other row that meets row $i$ inside $P$. The cases $n\le 2d$ (distance $0$), $n\le 2d+3$ (distance at most $3$) are already proved. The new layer is leftover at most $3$, i.e. $n=2d+4$.
--
--   If $u$ is not ridge-visible, its $d$ tight rows are far from $i$, and $z_1,z_2$ contribute at least $d+1$ near rows. The far leftover of a $\psi$-minimizing ridge-visible vertex $x$ and its decreasing neighbour $y$ therefore has size $r\le 3$. Matching ($r=1$), share-$(d-1)$ edges ($r=2$), and Extra$=B$ pigeonhole plus unique leave-one neighbours on dual-basis rays ($r=3$) produce a walk of length at most $r+1\le 4$, padded to $K$.
--
--   Both-miss at leftover $2$ puts $y$ in an open segment of $u$ and two leave-one neighbours, contradicting extremality. Leftover $3$ with Extra$=B$ forces the three omitted rays to enter the same unused row, so $y$ lies in an open segment of those neighbours.
--
--   $$
--   n\le 2d+4 \quad\Longrightarrow\quad \text{RV-distance}\le n-2d
--   $$
--   for simple bounded H-polytopes, on any row attained at two vertices.
--
--   This is the three-leftover layer of the ridge-visible recurrence. It does not treat $n\ge 2d+5$, and it does not by itself close the polynomial Hirsch conjecture.
--
--   **Formalization Note** Boundedness guarantees leave-one rays hit a new inequality. Dual-basis coordinates uniquely minimize the height at $u$. Two extreme points on the same open ray from a vertex coincide. Sharing $d-1$ tight rows produces an equality-face edge.
-- source:
--   Campaign research on ridge-visible access for the Polynomial Hirsch conjecture (2026-09-11). Companion to Hirsch.ridge_visible_neighbor_of_n_le_two_d_add_three. Novel three-leftover argument: Extra=B pigeonhole, unique leave-one neighbours on dual-basis rays, and a three-term open-segment contradiction.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem ridge_visible_neighbor_of_n_le_two_d_add_four
    {d n : ℕ} (hn : n ≤ 2 * d + 4)
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
    let K := n - 2 * d
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      w 0 = u ∧
      (⟪a i, w K⟫ = b i ∨
        ∃ r : Fin n, r ≠ i ∧ ⟪a r, w K⟫ = b r ∧
          ∃ x ∈ Hpoly a b, ⟪a i, x⟫ = b i ∧ ⟪a r, x⟫ = b r) ∧
      ∀ t < K,
        w t ∈ extremePoints ℝ (Hpoly a b) ∧
        w (t + 1) ∈ extremePoints ℝ (Hpoly a b) ∧
        (w t = w (t + 1) ∨ Adj (Hpoly a b) (w t) (w (t + 1))) := by sorry

end Hirsch
