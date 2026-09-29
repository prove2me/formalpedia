-- Prove2me | Theorems.Thm_tangent_projection_idempotent
-- name    : tangent_projection_idempotent
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-06-25T07:31:17.42276+00:00
-- url     : https://prove2.me/theorems/d72842de-7fea-4815-aff5-1a91b715b519
-- statement:
--   The orthogonal projection $P_T$ onto the tangent space at $M$ (defined from a rank-$r$ SVD via the left/right singular-space projectors) is idempotent: $P_T(P_T X)=P_T X$ for every matrix $X$. This follows from orthonormality of the singular vectors and is a reusable building block for operator-norm bounds on tangent-space sampling operators (Candes-Recht 2009, Section 3-4).
-- source:
--   Candes, Recht, Exact Matrix Completion via Convex Optimization (2009), Section 3

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2

open MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

theorem tangent_projection_idempotent
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (X : RealMatrix n1 n2) :
    tangentProjection S (tangentProjection S X) = tangentProjection S X := by sorry
