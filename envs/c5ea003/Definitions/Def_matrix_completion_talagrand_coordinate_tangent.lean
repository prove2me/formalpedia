-- Prove2me | Definitions.Def_matrix_completion_talagrand_coordinate_tangent
-- name    : matrix_completion_talagrand_coordinate_tangent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-25T06:30:58.546572+00:00
-- url     : https://prove2.me/theorems/f0b35a67-f156-46e9-bd2f-93be1da8e676
-- statement:
--   This definition stores the coordinate-expanded tangent-restricted supremum used between two Appendix 9.1 representation steps.
--
--   After Frobenius duality, the tangent sampling fluctuation is a bilinear expression with the second test matrix $X_2$ still constrained to the tangent space $T$.  Expanding $P_\Omega$ in the coordinate basis gives
--   $$
--   \sup_{\|X_1\|_F\le1,\ X_2\in T,\ \|X_2\|_F\le1}
--   \sum_{i,j}(\delta_{ij}-p)p^{-1}
--   \langle X_1,P_T(e_i e_j^\top)\rangle_F
--   \langle P_T(e_i e_j^\top),X_2\rangle_F.
--   $$
--   The Lean definition `tangentSamplingCoordinateTangentSupremumDeviation` records exactly this intermediate object, before the final step removes the tangent restriction on $X_2$.
--
--   Source location: Candes-Recht 2008, Appendix 9.1, PDF p. 46, immediately after equation (9.2).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand_tangent_bilinear

/-!
Coordinate-expanded tangent-restricted supremum from Candes-Recht Appendix 9.1.

This definition sits between the Frobenius-duality bilinear expression and the
unrestricted Talagrand supremum: the sampling fluctuation has already been
expanded in the coordinate basis, but the second test matrix is still required
to lie in the tangent space.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- Coordinate-expanded supremum with the second test matrix still restricted
to the tangent space. -/
noncomputable def tangentSamplingCoordinateTangentSupremumDeviation
    {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r) (p : Real) : Real :=
  sSup {v : Real |
    ∃ X1 X2 : RealMatrix n1 n2,
      frobeniusNorm X1 ≤ 1 ∧
        tangentProjection S X2 = X2 ∧
          frobeniusNorm X2 ≤ 1 ∧
            v =
              ∑ i : Fin n1, ∑ j : Fin n2,
                (((if (i, j) ∈ Omega then (1 : Real) else 0) - p) *
                  tangentSamplingTalagrandCoefficient S p X1 X2 i j)}

end MatrixCompletion


