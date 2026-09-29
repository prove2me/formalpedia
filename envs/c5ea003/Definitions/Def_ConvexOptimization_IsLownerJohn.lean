-- Prove2me | Definitions.Def_ConvexOptimization_IsLownerJohn
-- name    : ConvexOptimization_IsLownerJohn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-13T04:09:07.90645+00:00
-- url     : https://prove2.me/theorems/565135d2-5638-47f3-9217-aa665f0830c9
-- title:
--   Minimum-volume covering (Löwner–John) ellipsoid
-- statement:
--   The predicate singling out the minimum-volume covering ellipsoid — the *Löwner–John ellipsoid* — of a set of points in $\mathbb{R}^n$.
--
--   Let $S \subseteq \mathbb{R}^n$, let $A \in \mathbb{R}^{n\times n}$ and $b \in \mathbb{R}^n$, and write $\mathcal{E}(A,b) = \{v : \lVert Av + b\rVert_2 \le 1\}$ for the ellipsoid in quadratic-form guise. The pair $(A,b)$ is a *Löwner–John pair* for $S$ when
--
--   $$A = A^{T}, \qquad A \succ 0, \qquad S \subseteq \mathcal{E}(A,b), \qquad \det A' \le \det A \ \text{ for every } A' = A'^{T} \succ 0,\ b' \in \mathbb{R}^n \text{ with } S \subseteq \mathcal{E}(A',b').$$
--
--   The first two conditions say $(A,b)$ describes a genuine bounded ellipsoid, the third that it covers $S$, and the fourth that it is extremal: since $\operatorname{vol}\mathcal{E}(A,b) = \beta_n/\det A$ with $\beta_n$ the volume of the unit ball, maximizing $\det A$ over covering pairs is precisely minimizing the covered volume. This is problem (8.12) of Boyd & Vandenberghe.
--
--   Optimality is stated as a direct comparison of determinants against all competing covering pairs rather than through a volume functional, so the predicate needs no measure theory and can be used as a hypothesis without carrying an integration API. Note also that $b$ is unconstrained: the centre of the ellipsoid is the derived quantity $-A^{-1}b$.
--
--   **Formalization Note** `A.IsSymm` and `A.PosDef` are Mathlib's symmetry and positive-definiteness predicates, `S` is an arbitrary `Set (Fin n → ℝ)` (the statements of this mission instantiate it at the range of a finite family), and the extremality clause quantifies over all pairs `(A', b')` satisfying the same symmetry, definiteness and covering conditions.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 410-411, §8.4.1 eq. (8.10)-(8.11) (the minimum volume covering ellipsoid problem; minimizing volume is maximizing det A)

import Mathlib
import Definitions.Def_ConvexOptimization_ellipsoidBody

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace ConvexOptimization

/-- `(A, b)` is a minimum-volume (Löwner–John) covering ellipsoid of the point
set `S`: it is a PD symmetric covering ellipsoid maximizing `det A`. -/
def IsLownerJohn {nn : ℕ} (A : Matrix (Fin nn) (Fin nn) ℝ) (b : Fin nn → ℝ)
    (S : Set (Fin nn → ℝ)) : Prop :=
  A.IsSymm ∧ A.PosDef ∧ S ⊆ ellipsoidBody A b ∧
  ∀ (A' : Matrix (Fin nn) (Fin nn) ℝ) (b' : Fin nn → ℝ),
    A'.IsSymm → A'.PosDef → S ⊆ ellipsoidBody A' b' → A'.det ≤ A.det

end ConvexOptimization


