-- Prove2me | Theorems.Thm_ConvexOptimization_lowner_john_polytope_rounding
-- name    : ConvexOptimization.lowner_john_polytope_rounding
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T04:12:10.138551+00:00
-- url     : https://prove2.me/theorems/f992a0dd-65b4-4698-b073-05ca1526f9c5
-- title:
--   Löwner–John rounding for polytopes
-- statement:
--   **Löwner–John rounding for polytopes.** Shrinking the minimum-volume covering ellipsoid of a polytope about its centre by the factor $1/n$ lands inside the polytope.
--
--   Let $n \ge 1$, let $x_1,\dots,x_m \in \mathbb{R}^n$ and let $C = \operatorname{conv}\{x_1,\dots,x_m\}$. Let $(A,b)$ be a Löwner–John pair for the points: $A$ symmetric positive definite, $C \subseteq \mathcal{E} := \mathcal{E}(A,b) = \{v : \lVert Av + b\rVert_2 \le 1\}$, and $\det A$ maximal among all such covering pairs. Write $x_0 = -A^{-1}b$ for the centre of $\mathcal{E}$. Then
--
--   $$x_0 + \tfrac{1}{n}\bigl(\mathcal{E} - x_0\bigr) \;\subseteq\; C ,$$
--
--   that is, every $v \in \mathbb{R}^n$ with $\lVert Av + b\rVert_2 \le 1/n$ — equivalently $(Av+b)^{T}(Av+b) \le 1/n^{2}$ — belongs to $C$. Combined with the covering property $C \subseteq \mathcal{E}$ that is part of the hypothesis, the polytope is sandwiched between two concentric homothetic ellipsoids whose ratio is the dimension $n$.
--
--   This is the quantitative statement that a polytope can be *rounded*: after the affine change of coordinates taking $\mathcal{E}$ to the unit ball, $C$ lies between the balls of radius $1/n$ and $1$. Such a sandwich is what makes ellipsoid-method volume arguments and Banach–Mazur distance estimates work. The factor $n$ cannot be improved — it is attained by the simplex (Boyd & Vandenberghe, exercise 8.13) — and for general convex bodies, rather than polytopes, the same bound holds by an approximation argument.
--
--   **Formalization Note** The conclusion is stated in the scaled-preimage form $\lVert Av+b\rVert_2 \le 1/n$, using the dot product `⬝ᵥ` on `Fin n → ℝ`, so that no inverse $A^{-1}$ or explicit centre needs to appear; the covering hypothesis is imposed on the range of the family `x : Fin m → (Fin n → ℝ)`, which is equivalent to imposing it on $C$ because ellipsoids are convex. The dimension `nn` is assumed positive. Source: Boyd & Vandenberghe §8.4.1, p. 412.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 412, 449, §8.4.1 (Loewner-John rounding: shrinking the covering ellipsoid by the factor 1/n about its centre lands inside the polytope); tightness on simplices is exercise 8.13

import Mathlib
import Definitions.Def_ConvexOptimization_ellipsoidBody
import Definitions.Def_ConvexOptimization_IsLownerJohn

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.lowner_john_polytope_rounding {nn m : ℕ} (hnn : 0 < nn)
    (x : Fin m → Fin nn → ℝ) (A : Matrix (Fin nn) (Fin nn) ℝ) (b : Fin nn → ℝ)
    (hopt : IsLownerJohn A b (Set.range x)) (v : Fin nn → ℝ)
    (hv : (A.mulVec v + b) ⬝ᵥ (A.mulVec v + b) ≤ 1 / (nn : ℝ) ^ 2) :
    v ∈ convexHull ℝ (Set.range x) := by
  sorry
