-- Prove2me | Definitions.Def_matrix_completion_schatten
-- name    : matrix_completion_schatten
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-13T22:56:25.54116+00:00
-- url     : https://prove2.me/theorems/922f2169-8a3f-499f-ae1c-3d7f5ccb1212
-- statement:
--   This definition module provides Schatten-moment helper objects for converting Rademacher and matrix concentration estimates into spectral norm bounds.
--
--   $$
--   \|A\|_{S_q}=\left(\sum_k \sigma_k(A)^q\right)^{1/q}.
--   $$
--
--   Module overview: Schatten norms for finite real matrices. Section 6.1 compares the operator norm to the Schatten $q$-norm and then applies the noncommutative Khintchine inequality in Schatten norm. Mathlib already provides singular values for finite-dimensional linear maps; this file packages the corresponding finite matrix norm used by the paper.
--
--   Documented declarations:
--   1. Schatten $q$-norm of a real matrix, written using the singular values of the associated Euclidean linear map. The exponent is real-valued so the paper's $q \ge \log n$ comparisons can be stated directly.
--
--   Role in the mission. Key declarations include schattenNorm. These definitions provide shared vocabulary for the Exact Matrix Completion decomposition, so theorem statements can refer to sampling models, recovery events, tangent-space geometry, and concentration estimates without restating the infrastructure each time.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent

/-!
Schatten norms for finite real matrices.

Section 6.1 compares the operator norm to the Schatten `q`-norm and then
applies the noncommutative Khintchine inequality in Schatten norm.  Mathlib
already provides singular values for finite-dimensional linear maps; this file
packages the corresponding finite matrix norm used by the paper.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- Schatten `q`-norm of a real matrix, written using the singular values of
the associated Euclidean linear map.  The exponent is real-valued so the paper's
`q ≥ log n` comparisons can be stated directly. -/
noncomputable def schattenNorm {n1 n2 : Nat} (q : Real)
    (X : RealMatrix n1 n2) : Real :=
  Real.rpow
    (∑ k : Fin n2,
      Real.rpow ((Matrix.toEuclideanLin X).singularValues k) q)
    q⁻¹

end MatrixCompletion


