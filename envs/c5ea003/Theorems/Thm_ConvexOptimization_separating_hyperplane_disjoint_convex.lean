-- Prove2me | Theorems.Thm_ConvexOptimization_separating_hyperplane_disjoint_convex
-- name    : ConvexOptimization.separating_hyperplane_disjoint_convex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-11T21:38:07.691412+00:00
-- url     : https://prove2.me/theorems/1eae9652-bccc-477e-9bd9-3757a2b32fd7
-- title:
--   Separating hyperplane theorem
-- statement:
--   **The separating hyperplane theorem.**
--
--   Let $C$ and $D$ be nonempty convex subsets of $\mathbb{R}^n$ that are disjoint, $C \cap D = \emptyset$. Then there is a hyperplane separating them: there exist a nonzero vector $a \in \mathbb{R}^n$ and a scalar $b \in \mathbb{R}$ with
--
--   $$\langle a, x\rangle \le b \quad \text{for every } x \in C, \qquad\text{and}\qquad \langle a, x\rangle \ge b \quad \text{for every } x \in D .$$
--
--   The separation is not asserted to be strict — with only convexity and disjointness in hand, the two sets may touch in the limit (as do $\{(x,y) : y \le 0\}$ and $\{(x,y) : x > 0,\ y \le 1/x\}$), and strictness requires an additional hypothesis such as compactness of one set and closedness of the other.
--
--   This is the geometric foundation of the whole duality theory: strong duality, supporting hyperplanes, theorems of the alternative, and the existence of subgradients are all obtained by separating a suitable pair of convex sets. It is the single most reused statement of Chapter 2.
--
--   **Formalization Note** Vectors live in `EuclideanSpace ℝ (Fin n)`; the conclusion is an existential over `a ≠ 0` and `b`, with the two families of inequalities stated pointwise. Source: B&V §2.5.1, pp. 46–48.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 46-48, §2.5.1 (separating hyperplane theorem)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.separating_hyperplane_disjoint_convex {n : ℕ}
    (C D : Set (EuclideanSpace ℝ (Fin n)))
    (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hCne : C.Nonempty) (hDne : D.Nonempty) (hdisj : Disjoint C D) :
    ∃ a : EuclideanSpace ℝ (Fin n), a ≠ 0 ∧ ∃ b : ℝ,
      (∀ x ∈ C, ⟪a, x⟫ ≤ b) ∧ (∀ x ∈ D, b ≤ ⟪a, x⟫) := by
  sorry
