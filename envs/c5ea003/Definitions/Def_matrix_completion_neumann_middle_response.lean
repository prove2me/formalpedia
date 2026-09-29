-- Prove2me | Definitions.Def_matrix_completion_neumann_middle_response
-- name    : matrix_completion_neumann_middle_response
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-01T14:21:08.587191+00:00
-- url     : https://prove2.me/theorems/545a99a3-159c-4eb0-9adc-44c5483e0df5
-- statement:
--   Defines the middle-index off-diagonal response operator and all-ones matrix used for the Candes-Recht 2008 Section 6.3 mean subterm for the omega_1 = omega_3 != omega_2 case.
-- source:
--   Candes-Recht 2008, Section 6.3, PDF pp. 32--33, equation (6.20).

import Definitions.Def_matrix_completion_neumann

/-!
Off-diagonal response operator for the MEAN part of the `ω₁ = ω₃ ≠ ω₂`
quadratic Neumann term (Candès–Recht 2008, §6.3, eq. (6.20)).

The parent `Def_matrix_completion_neumann` file is already at its size cap, so
this single reusable operator lives in its own file.  It is the middle-index
analogue of `quadraticLastIndexDistinctOffDiagonalResponse`: the fluctuation
now enters through the summed index `ω₂`, the output carries the sign matrix
`E_{ω₁}`, and the tangent weight is the kernel-square
`⟪P_T e_{ω₁}, e_{ω₂}⟫ ⟪P_T e_{ω₂}, e_{ω₁}⟫`.
-/

namespace MatrixCompletion

/-- Off-diagonal response operator for the mean part of the
`ω₁ = ω₃ ≠ ω₂` quadratic contribution.  Applied to
`p^{-1}(P_Ω - pI)(p^{-1} 𝟙)`, this reproduces the mean subterm of (6.20)
after the `ξ_{ω₁}²` expansion, with the diagonal `ω₁ = ω₂` terms removed. -/
noncomputable def quadraticMiddleIndexDistinctOffDiagonalResponse
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (X : RealMatrix n1 n2) : RealMatrix n1 n2 :=
  ∑ w1 : Fin n1 × Fin n2,
    ∑ w2 : Fin n1 × Fin n2,
      if w1 = w2 then 0 else
        (X w2.1 w2.2 *
          signMatrix S w1.1 w1.2 *
            tangentCoordinateKernel S w1.1 w1.2 w2.1 w2.2 *
              tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2) •
          coordinateMatrix w1.1 w1.2

/-- The all-ones fixed matrix, used to feed the constant `ω₂`-fluctuation into
the middle-index response operator. -/
noncomputable def onesMatrix (n1 n2 : Nat) : RealMatrix n1 n2 := fun _ _ => 1

end MatrixCompletion


