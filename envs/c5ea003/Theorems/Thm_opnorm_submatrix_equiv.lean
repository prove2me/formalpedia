-- Prove2me | Theorems.Thm_opnorm_submatrix_equiv
-- name    : opnorm_submatrix_equiv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-24T17:06:37.522406+00:00
-- url     : https://prove2.me/theorems/e66e5c47-13ad-4b72-b5b0-21a5c9d72602
-- statement:
--   **L2 operator norm is invariant under simultaneous reindexing.**
--
--   Let $e:\alpha\simeq\beta$ be an equivalence of finite index types. For a real square matrix $A$ indexed by $\beta$, reindexing both rows and columns by $e$ produces the conjugate matrix $A.submatrix\ e\ e$ on $\alpha$. The theorem states
--   $$
--   \left\|\operatorname{toEuclideanLin}(A.submatrix\ e\ e)\right\|
--   =
--   \left\|\operatorname{toEuclideanLin}(A)\right\|.
--   $$
--   Equivalently, permutation-conjugate matrices define isometric Euclidean linear maps and therefore have the same L2 operator norm. This is the index bridge needed when the Rudelson tangent-coordinate space `Fin n₁ × Fin n₂` is identified with a single `Fin (n₁n₂)` index for general matrix Rademacher inequalities.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.NormedSpace

open scoped Matrix.Norms.L2Operator
open Matrix

set_option maxHeartbeats 1000000

/-- Simultaneous row-and-column reindexing by an equivalence preserves the L2
operator norm of the corresponding Euclidean matrix operator. -/

theorem opnorm_submatrix_equiv {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (A : Matrix β β ℝ) :
    ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (A.submatrix e e)))‖
      = ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A))‖ := by
  sorry
