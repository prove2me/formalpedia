-- Prove2me | Theorems.Thm_ConvexOptimization_lowner_john_affine_invariant
-- name    : ConvexOptimization.lowner_john_affine_invariant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T04:11:40.363867+00:00
-- url     : https://prove2.me/theorems/9ef4eb79-6643-4bc6-96b8-78d1dcc04eb0
-- title:
--   Affine invariance of the Löwner–John ellipsoid
-- statement:
--   The Löwner–John ellipsoid commutes with nonsingular affine changes of coordinates.
--
--   Let $S \subseteq \mathbb{R}^n$, let $T \in \mathbb{R}^{n \times n}$ be invertible, let $t \in \mathbb{R}^n$, and write $\Phi(v) = Tv + t$ for the corresponding affine bijection. If $(A,b)$ is a Löwner–John pair for $S$, then the image set $\Phi(S)$ also admits a Löwner–John pair $(A',b')$, and its ellipsoid is the affine image of the original:
--
--   $$\mathcal{E}(A',b') \;=\; \Phi\bigl(\mathcal{E}(A,b)\bigr), \qquad \mathcal{E}(A,b) = \{v : \lVert Av+b\rVert_2 \le 1\}.$$
--
--   (Concretely one may take $A' = A T^{-1}$ and $b' = b - A T^{-1} t$, which is again symmetric-positive-definite up to the normalization built into the predicate.)
--
--   Affine invariance is what makes the normalization step of this mission legitimate: an arbitrary configuration can be mapped so that its Löwner–John ellipsoid becomes the unit ball, where the KKT identities take their clean isotropic form, and the conclusion transported back. It also shows the rounding factor $1/n$ is an affine invariant of the body, not an artefact of a particular position — determinant ratios, unlike volumes, are unchanged by $\Phi$.
--
--   **Formalization Note** Nonsingularity is stated as `IsUnit T.det`; the image is `(fun v => T.mulVec v + t) '' S`. The conclusion is existential in $(A',b')$ together with the set identity, even though uniqueness makes the pair determined. Source: Boyd & Vandenberghe §8.4.3, pp. 415–416.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 415-416, §8.4.3 (affine invariance of the extremal volume ellipsoids)

import Mathlib
import Definitions.Def_ConvexOptimization_ellipsoidBody
import Definitions.Def_ConvexOptimization_IsLownerJohn

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.lowner_john_affine_invariant {nn : ℕ}
    (T : Matrix (Fin nn) (Fin nn) ℝ) (hT : IsUnit T.det) (t : Fin nn → ℝ)
    (S : Set (Fin nn → ℝ)) (A : Matrix (Fin nn) (Fin nn) ℝ) (b : Fin nn → ℝ)
    (h : IsLownerJohn A b S) :
    ∃ (A' : Matrix (Fin nn) (Fin nn) ℝ) (b' : Fin nn → ℝ),
      IsLownerJohn A' b' ((fun v => T.mulVec v + t) '' S) ∧
      ellipsoidBody A' b' = (fun v => T.mulVec v + t) '' ellipsoidBody A b := by
  sorry
