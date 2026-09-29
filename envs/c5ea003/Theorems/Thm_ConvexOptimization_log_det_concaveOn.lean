-- Prove2me | Theorems.Thm_ConvexOptimization_log_det_concaveOn
-- name    : ConvexOptimization.log_det_concaveOn
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-11T21:42:28.720573+00:00
-- url     : https://prove2.me/theorems/36f0e813-df50-4df7-9791-ecae7cd3b8f8
-- title:
--   Concavity of $\log\det$
-- statement:
--   **Concavity of $\log\det$ on the positive definite cone.**
--
--   On the set of symmetric positive definite $n \times n$ real matrices, the function
--
--   $$A \;\longmapsto\; \log \det A$$
--
--   is concave: $\log\det(\theta A + (1-\theta)B) \ge \theta \log\det A + (1-\theta)\log\det B$ for positive definite $A, B$ and $\theta \in [0,1]$.
--
--   Equivalently $-\log\det$ is convex — it is the standard *barrier function* for the semidefinite cone, and the reason interior-point methods for semidefinite programs work. The same function is the log-likelihood of a centred Gaussian in terms of the precision matrix, so concavity is what makes maximum-likelihood covariance estimation a convex problem, and it is the objective whose maximization defines the Löwner–John ellipsoid.
--
--   **Formalization Note** The domain is the set `{A : Matrix (Fin n) (Fin n) ℝ | A.PosDef}` inside the space of all matrices, and concavity is Mathlib's `ConcaveOn ℝ`; positive definiteness in Mathlib includes symmetry (Hermitian-ness), so no separate symmetry hypothesis appears. Source: B&V §3.1.5, p. 74.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 73, §3.1.5 Examples, the Log-determinant item (f(X) = log det X is concave on the PD cone)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.log_det_concaveOn {n : ℕ} :
    ConcaveOn ℝ {A : Matrix (Fin n) (Fin n) ℝ | A.PosDef}
      (fun A => Real.log A.det) := by
  sorry
