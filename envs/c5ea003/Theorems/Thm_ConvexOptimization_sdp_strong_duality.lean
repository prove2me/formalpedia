-- Prove2me | Theorems.Thm_ConvexOptimization_sdp_strong_duality
-- name    : ConvexOptimization.sdp_strong_duality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T16:03:58.354297+00:00
-- url     : https://prove2.me/theorems/9bfde6b7-09b1-455c-a535-cabf13480484
-- title:
--   SDP strong duality
-- statement:
--   **Strong duality for the inequality-form semidefinite program.**
--
--   Consider, with variable $x \in \mathbb{R}^n$ and symmetric $k \times k$ data $F_1,\dots,F_n, G$,
--
--   $$\text{minimize } c^{T}x \quad\text{subject to}\quad G + \sum_{i=1}^{n} x_i F_i \preceq 0 .$$
--
--   Assume strict feasibility — some $\tilde{x}$ makes $G + \sum_i \tilde{x}_i F_i$ negative definite — and that the optimal value is finite. Then the dual optimum is attained: there is a symmetric $Z \succeq 0$ with
--
--   $$\operatorname{tr}(F_i Z) + c_i = 0 \quad (i = 1,\dots,n), \qquad \operatorname{tr}(GZ) \;=\; p^{\star},$$
--
--   where $p^{\star}$ is the optimal value of the primal.
--
--   Semidefinite programming inherits strong duality from the conic theorem because the positive semidefinite cone is closed, convex and has nonempty interior, and the strict-feasibility hypothesis is exactly the generalized Slater condition for it. The dual variable $Z$ is a matrix rather than a vector, and the equality constraints $\operatorname{tr}(F_iZ) = -c_i$ are the conic analogue of dual feasibility.
--
--   **Formalization Note** Matrices are `Matrix (Fin k) (Fin k) ℝ` with symmetry `IsSymm`; the semidefinite inequality $M \preceq 0$ appears as `(-M).PosSemidef`, strict feasibility as `PosDef`, and the trace pairing as `(F i * Z).trace`. The optimal value is an `sInf` over the image of the feasible set, guarded by `BddBelow`. Source: B&V §5.9.2, pp. 265–266.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 265-266, §5.9.2 (semidefinite programming duality; the inequality-form SDP example)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.sdp_strong_duality {n nn : ℕ} (c : Fin n → ℝ)
    (F : Fin n → Matrix (Fin nn) (Fin nn) ℝ) (hF : ∀ i, (F i).IsSymm)
    (G : Matrix (Fin nn) (Fin nn) ℝ) (hG : G.IsSymm)
    (xs : Fin n → ℝ) (hxs : (-(G + ∑ i, xs i • F i)).PosDef)
    (hbdd : BddBelow ((fun x : Fin n → ℝ => c ⬝ᵥ x) ''
      {x | (-(G + ∑ i, x i • F i)).PosSemidef})) :
    ∃ Z : Matrix (Fin nn) (Fin nn) ℝ, Z.PosSemidef ∧
      (∀ i, ((F i) * Z).trace + c i = 0) ∧
      (G * Z).trace =
        sInf ((fun x : Fin n → ℝ => c ⬝ᵥ x) ''
          {x | (-(G + ∑ i, x i • F i)).PosSemidef}) := by
  sorry
