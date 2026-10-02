-- Prove2me | Definitions.Def_BookSixthRotations
-- name    : BookSixthRotations
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-26T00:53:37.975409+00:00
-- url     : https://prove2.me/theorems/10475e72-a40a-455d-b587-1924bf0a7707

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

noncomputable section

/-!
Coordinate-plane rotations of `Space3 = Fin 3 -> R`, as explicit 3x3 matrices
and as continuous linear maps.

Continuity is discharged by `LinearMap.continuous_of_finiteDimensional`, valid
because `Fin 3 -> R` is finite-dimensional over `R`; this avoids asking `fun_prop`
to see through a matrix. The matrix route is necessary because
`ContinuousLinearMap.pi` takes a family whose source is a coordinate type and so
builds a DIAGONAL operator, which cannot mix coordinates and hence cannot express
a rotation.
-/

/-- The `01`-rotation, as an explicit `3 × 3` matrix. -/
def rot01Matrix (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![Real.cos θ, -Real.sin θ, 0],
    ![Real.sin θ, Real.cos θ, 0],
    ![0, 0, 1]]

/-- The `02`-rotation matrix. -/
def rot02Matrix (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![Real.cos θ, 0, -Real.sin θ],
    ![0, 1, 0],
    ![Real.sin θ, 0, Real.cos θ]]

/-- The `12`-rotation matrix. -/
def rot12Matrix (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1, 0, 0],
    ![0, Real.cos θ, -Real.sin θ],
    ![0, Real.sin θ, Real.cos θ]]

/-- The `01`-rotation, as a continuous linear map on `Space3`.

Continuity is discharged by `LinearMap.continuous_of_finiteDimensional`, which applies
because `Space3 = Fin 3 → ℝ` is finite-dimensional over `ℝ`; this avoids asking `fun_prop`
to see through a matrix. -/
def rot01CLM (θ : ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  { toLinearMap := rot01Matrix θ |>.mulVecLin
    cont := (rot01Matrix θ).mulVecLin.continuous_of_finiteDimensional }

end


