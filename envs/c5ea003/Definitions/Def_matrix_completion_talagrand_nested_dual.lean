-- Prove2me | Definitions.Def_matrix_completion_talagrand_nested_dual
-- name    : matrix_completion_talagrand_nested_dual
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-25T06:42:38.143928+00:00
-- url     : https://prove2.me/theorems/a9e075de-ca5d-4d36-b852-c677894e8ddb
-- statement:
--   This definition records the nested Frobenius-dual supremum that appears when the norm in the tangent sampling deviation is dualized.
--
--   For a fixed tangent Frobenius-unit matrix $X_2$, Frobenius duality rewrites
--   $$
--   p^{-1}\|P_TP_\Omega X_2-pX_2\|_F
--   $$
--   as the supremum over Frobenius-unit test matrices $X_1$ of
--   $$
--   p^{-1}\langle X_1,P_TP_\Omega X_2-pX_2\rangle_F.
--   $$
--   The definition `tangentSamplingNestedDualDeviation` keeps the outer supremum over tangent $X_2$ and the inner supremum over $X_1$ separate.  The next formal lemma flattens this nested supremum into the two-test-matrix bilinear supremum.
--
--   Source location: Candes-Recht 2008, Appendix 9.1, PDF p. 46, immediately after equation (9.2), where the paper writes $Z=\sup\langle X_1,Y(X_2)\rangle$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand_tangent_bilinear

/-!
Nested Frobenius-dual supremum for the Appendix 9.1 representation.

This definition is the direct result of applying Frobenius duality to the norm
inside `tangentSamplingDeviation`, while keeping the outer supremum over
tangent unit matrices separate.  The next formal step flattens this nested
supremum into the two-test-matrix bilinear supremum.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- Nested dual form of the tangent sampling deviation.

For each tangent Frobenius-unit matrix `X2`, the inner supremum dualizes the
Frobenius norm of `P_T P_Omega X2 - p X2` against Frobenius-unit test matrices
`X1`. -/
noncomputable def tangentSamplingNestedDualDeviation
    {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r) (p : Real) : Real :=
  sSup {v : Real |
    ∃ X2 : RealMatrix n1 n2,
      tangentProjection S X2 = X2 ∧
        frobeniusNorm X2 ≤ 1 ∧
          v =
            sSup {w : Real |
              ∃ X1 : RealMatrix n1 n2,
                frobeniusNorm X1 ≤ 1 ∧
                  w =
                    p⁻¹ *
                      matrixInner X1
                        (tangentProjection S (samplingProjection Omega X2) -
                          p • X2)}}

end MatrixCompletion


