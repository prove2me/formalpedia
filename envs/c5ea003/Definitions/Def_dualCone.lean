-- Prove2me | Definitions.Def_dualCone
-- name    : dualCone
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-11T21:36:18.814364+00:00
-- url     : https://prove2.me/theorems/b88f161a-d1a9-4370-94fe-03800ceba7b5
-- title:
--   Dual cone $K^*$
-- statement:
--   The **dual cone** of a set of vectors.
--
--   For $K \subseteq \mathbb{R}^n$, the dual cone is
--
--   $$K^{*} \;=\; \{\, y \in \mathbb{R}^n \;:\; \langle x, y\rangle \ge 0 \ \text{ for every } x \in K \,\},$$
--
--   the set of vectors making a non-obtuse angle with every element of $K$ — equivalently, the normals of all homogeneous halfspaces containing $K$.
--
--   $K^{*}$ is always a closed convex cone, whatever $K$ is: it is an intersection of homogeneous halfspaces, one for each $x \in K$. Dual cones are the language of conic programming — the generalized inequality $\preceq_K$ has $\preceq_{K^{*}}$ as its dual — and the dual cone of the positive semidefinite cone, of the nonnegative orthant and of the second-order cone are each self-dual, which is why those three cones dominate practice.
--
--   **Formalization Note** Ambient vectors live in `EuclideanSpace ℝ (Fin n)` with its standard inner product; the definition places no hypothesis on `K`, which need be neither convex nor a cone. Source: B&V §2.6.1, p. 51.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 51, §2.6.1 (definition of the dual cone K*)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace ConvexOptimization

/-- **Dual cone** of a set `K ⊆ ℝⁿ` (B&V §2.6.1): `K* = {y | ⟪x, y⟫ ≥ 0 ∀ x ∈ K}`. -/
def dualCone {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ x ∈ K, 0 ≤ ⟪x, y⟫}

end ConvexOptimization


