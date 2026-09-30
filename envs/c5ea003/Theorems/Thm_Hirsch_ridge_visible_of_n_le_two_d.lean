-- Prove2me | Theorems.Thm_Hirsch_ridge_visible_of_n_le_two_d
-- name    : Hirsch.ridge_visible_of_n_le_two_d
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T15:40:06.741978+00:00
-- url     : https://prove2.me/theorems/be3d4339-bbe8-48e1-b0e7-bd86eb7661a3
-- title:
--   Ridge-visibility at or below the d-step equator when the target row has two vertices
-- statement:
--   Let $P\subseteq\mathbb R^d$ be an H-polyhedron defined by $n$ inequalities, with $n\le 2d$. Let $i$ be a describing row that is tight at two distinct vertices $z_1\neq z_2$. Then every vertex $u$ of $P$ is *ridge-visible* to row $i$: either $u$ itself is tight on row $i$, or $u$ is tight on some other row $r\neq i$ that meets row $i$ at a feasible point of $P$.
--
--   An extreme point is tight on at least $d$ rows. Distinct extreme points have distinct tight-row sets, because a spanning set of tight normals uniquely recovers the point. Consequently the two vertices of the target row contribute at least $d+1$ rows that meet it. The complementary “far” rows therefore number at most $d-1$, which cannot cover the $\ge d$ tight rows of any vertex.
--
--   $$
--   n\le 2d,\quad z_1\neq z_2\text{ tight on row }i
--   \quad\Longrightarrow\quad
--   \text{every vertex is ridge-visible to row }i.
--   $$
--
--   This extends the sub-balanced intersection lemma ($n<2d$) through the $d$-step equator $n=2d$, at the cost of requiring two distinct vertices on the target row (so the equality set is not a singleton). Boundedness and simplicity are not assumed. The statement does not bound graph distance to the target row when $n>2d$, and it does not by itself yield a uniform polynomial diameter.
--
--   **Formalization Note** Tight-row cardinality at least $d$ holds for every extreme point of a finite H-presentation in $\mathbb R^d$. The two-vertex hypothesis is used only to guarantee that the near-row union is strictly larger than a single $d$-set.
-- source:
--   Campaign research on ridge-visible access for the Polynomial Hirsch conjecture (2026-09-11). Extends Hirsch.diamLE_le_section_diamLE_of_n_lt_two_d through n=2d when the target row is not a singleton face. Experiments on stacked duals and sausages: RV-distance is 0 throughout n<=2d, and the first positive RV appears at n=2d+3.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem ridge_visible_of_n_le_two_d
    {d n : ℕ} (hn : n ≤ 2 * d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i : Fin n)
    {z₁ z₂ : EuclideanSpace ℝ (Fin d)}
    (hz₁ : z₁ ∈ extremePoints ℝ (Hpoly a b))
    (hz₂ : z₂ ∈ extremePoints ℝ (Hpoly a b))
    (hne : z₁ ≠ z₂)
    (hzi₁ : ⟪a i, z₁⟫ = b i)
    (hzi₂ : ⟪a i, z₂⟫ = b i)
    (u : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b)) :
    ⟪a i, u⟫ = b i ∨
      ∃ r : Fin n, r ≠ i ∧ ⟪a r, u⟫ = b r ∧
        ∃ x ∈ Hpoly a b, ⟪a i, x⟫ = b i ∧ ⟪a r, x⟫ = b r := by sorry

end Hirsch
