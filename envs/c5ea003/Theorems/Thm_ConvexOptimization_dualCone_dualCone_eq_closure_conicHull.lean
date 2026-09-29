-- Prove2me | Theorems.Thm_ConvexOptimization_dualCone_dualCone_eq_closure_conicHull
-- name    : ConvexOptimization.dualCone_dualCone_eq_closure_conicHull
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-11T21:39:18.439126+00:00
-- url     : https://prove2.me/theorems/c77ac89b-0c43-4b6d-b15e-76ad85c358fa
-- title:
--   Double dual cone = closed conic hull
-- statement:
--   **The double dual cone is the closed conic hull.**
--
--   For an arbitrary $K \subseteq \mathbb{R}^n$, write $K^{*} = \{y : \langle x,y\rangle \ge 0 \ \forall x \in K\}$ for the dual cone and $\operatorname{cone}(K)$ for the set of all finite nonnegative combinations of elements of $K$. Then
--
--   $$K^{**} \;=\; \overline{\operatorname{cone}(K)} .$$
--
--   Dualizing twice is therefore a closure operation, not the identity: it adds exactly the nonnegative combinations of the elements of $K$ and then the limit points. In particular $K^{**} = K$ precisely when $K$ is a closed convex cone, which is the conic analogue of the Fenchel–Moreau theorem for functions.
--
--   The identity is what licenses moving between a cone described by generators and the same cone described by inequalities — the two representations of conic constraints used throughout conic and semidefinite programming.
--
--   **Formalization Note** Both `dualCone` and `conicHull` are the mission's own definitions, and no hypothesis is placed on `K` — the theorem holds for every subset, with the closure and the conic hull doing all the work. Source: B&V §2.6.1, p. 53, and exercise 2.31(e), p. 64.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 53, 64, §2.6.1 (dual cones of dual cones) and exercise 2.31(e)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_conicHull

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.dualCone_dualCone_eq_closure_conicHull {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) :
    dualCone (dualCone K) = closure (conicHull K) := by
  sorry
