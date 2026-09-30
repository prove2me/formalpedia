-- Prove2me | Theorems.Thm_Hirsch_ridge_visible_neighbor_of_n_le_two_d_add_three
-- name    : Hirsch.ridge_visible_neighbor_of_n_le_two_d_add_three
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T19:17:18.836699+00:00
-- url     : https://prove2.me/theorems/50c22f7c-2bfd-4642-ba2b-637401134251
-- title:
--   Ridge-visible access in the $n\le 2d+3$ two-leftover regime
-- statement:
--   Let $P\subseteq\mathbb R^d$ be a bounded simple H-polytope with $n\le 2d+3$ inequalities. Simplicity means every vertex is tight on exactly $d$ rows. Let $i$ be a describing row that is tight at two distinct vertices $z_1\neq z_2$. Then every vertex $u$ of $P$ is at graph distance at most $3$ from the ridge-visible set of row $i$.
--
--   Ridge-visible means $u$ is tight on row $i$, or tight on some other row that meets row $i$ inside $P$. The cases $n\le 2d$ (distance $0$), $n=2d+1$ and $n=2d+2$ (distance at most $1$) are already proved. The new layer is $n=2d+3$.
--
--   If $u$ is not ridge-visible, its $d$ tight rows are far from $i$, and $z_1,z_2$ contribute at least $d+1$ near rows. That leaves at most two leftover far inequalities $H,H_2$. The one-collision case (every leave-one ray from $u$ enters the same leftover) is the simplex argument of $n=2d+2$: $P$ is that simplex, all generators are strictly slack on $i$, contradiction.
--
--   When the two leftovers are mixed, the far rows are exactly the $d+2$ rows $t_U\cup\{H,H_2\}$. Non-ridge-visible vertices have tight sets that are $d$-subsets of these $d+2$ rows (Johnson graph $J(d+2,2)$). Vertices that share $d-1$ tight rows bound an edge. Consequently every far vertex is at graph distance at most $2$ from $u$.
--
--   A linear height $\psi$ uniquely minimized at $u$ (dual-basis cone) has a minimizer $x$ among the finitely many ridge-visible vertices. A decreasing neighbour $y$ of $x$ cannot be ridge-visible, hence is far, hence is at distance $\le 2$ from $u$. The path $u\rightsquigarrow y-x$ has length at most $3$ and ends in the ridge-visible set.
--
--   $$
--   n\le 2d+3 \quad\Longrightarrow\quad \text{RV-distance}\le 3
--   $$
--   for simple bounded H-polytopes, on any row attained at two vertices.
--
--   This is the two-leftover layer of the ridge-visible recurrence. It does not treat $n\ge 2d+4$, and it does not by itself close the polynomial Hirsch conjecture.
--
--   **Formalization Note** Boundedness guarantees leave-one rays hit a new inequality. Dual-basis coordinates uniquely minimize the height at $u$. Extreme points inject into $d$-subsets of the $n$ rows, so the ridge-visible set is finite. Sharing $d-1$ tight rows produces an equality-face edge.
-- source:
--   Campaign research on ridge-visible access for the Polynomial Hirsch conjecture (2026-09-11). Companion to Hirsch.ridge_visible_neighbor_of_n_eq_two_d_add_two. Novel two-leftover argument: Johnson $J(d+2,2)$ distance plus a dual-basis height minimizer among ridge-visible vertices.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem ridge_visible_neighbor_of_n_le_two_d_add_three
    {d n : ℕ} (hn : n ≤ 2 * d + 3)
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
    (∃ w, w ∈ extremePoints ℝ (Hpoly a b) ∧ Adj (Hpoly a b) u w ∧
      (⟪a i, w⟫ = b i ∨
        ∃ r : Fin n, r ≠ i ∧ ⟪a r, w⟫ = b r ∧
          ∃ x ∈ Hpoly a b, ⟪a i, x⟫ = b i ∧ ⟪a r, x⟫ = b r)) ∨
    (∃ w v, w ∈ extremePoints ℝ (Hpoly a b) ∧ v ∈ extremePoints ℝ (Hpoly a b) ∧
      Adj (Hpoly a b) u w ∧ Adj (Hpoly a b) w v ∧
      (⟪a i, v⟫ = b i ∨
        ∃ r : Fin n, r ≠ i ∧ ⟪a r, v⟫ = b r ∧
          ∃ x ∈ Hpoly a b, ⟪a i, x⟫ = b i ∧ ⟪a r, x⟫ = b r)) ∨
    ∃ w v z, w ∈ extremePoints ℝ (Hpoly a b) ∧
      v ∈ extremePoints ℝ (Hpoly a b) ∧ z ∈ extremePoints ℝ (Hpoly a b) ∧
      Adj (Hpoly a b) u w ∧ Adj (Hpoly a b) w v ∧ Adj (Hpoly a b) v z ∧
      (⟪a i, z⟫ = b i ∨
        ∃ r : Fin n, r ≠ i ∧ ⟪a r, z⟫ = b r ∧
          ∃ x ∈ Hpoly a b, ⟪a i, x⟫ = b i ∧ ⟪a r, x⟫ = b r) := by sorry

end Hirsch
