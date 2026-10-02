-- Prove2me | solution 1 for BookSixth.threefold_rotation_preserves_inner_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-26T03:04:55.317123+00:00
-- url     : https://prove2.me/submissions/8c06f75b-b4bb-4e03-ac84-1c28611180cd

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthRotations3

-- Coordinate-plane rotations of `Space3 = Fin 3 -> R` as continuous linear maps, and the
-- inner-product preservation that makes them admissible in the roundness lemmas.
--
-- The rotations are built as `3x3` matrices lifted through `Matrix.mulVecLin` rather than
-- through `ContinuousLinearMap.pi`. That is deliberate: `ContinuousLinearMap.pi` (at
-- `Mathlib/Topology/Algebra/Module/ContinuousLinearMap/PiProd.lean:268`) takes a family
-- `forall i, (phi i) ->L[R] (psi i)` where `phi i` is a COORDINATE TYPE, so each component
-- map is out of the scalar field. It therefore builds a DIAGONAL operator, which cannot
-- compute coordinate 0 from coordinate 1, and so cannot express a rotation at all. The
-- matrix route is the correct one, and continuity comes from
-- `LinearMap.continuous_of_finiteDimensional`, which applies because `Fin 3 -> R` is
-- finite-dimensional over `R`.

open scoped BigOperators
open scoped Matrix
open BookSixth
open Matrix



-- ## The inner-product-preserving linear part

set_option maxHeartbeats 2000000 in
/-- The `01`-rotation matrix acts by the explicit rotation formula. -/
theorem rot01Matrix_apply (θ : ℝ) (x : Fin 3 → ℝ) :
    Matrix.mulVec (rot01Matrix θ) x
      = ![Real.cos θ * x 0 - Real.sin θ * x 1,
          Real.sin θ * x 0 + Real.cos θ * x 1, x 2] := by
  funext i
  fin_cases i <;>
    simp only [rot01Matrix, Matrix.mulVec] <;>
    rw [Matrix.vec3_dotProduct] <;>
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Matrix.vecEmpty] <;>
    ring

set_option maxHeartbeats 2000000 in
/-- The `02`-rotation matrix acts by the explicit rotation formula. -/
theorem rot02Matrix_apply (θ : ℝ) (x : Fin 3 → ℝ) :
    Matrix.mulVec (rot02Matrix θ) x
      = ![Real.cos θ * x 0 - Real.sin θ * x 2, x 1,
          Real.sin θ * x 0 + Real.cos θ * x 2] := by
  funext i
  fin_cases i <;>
    simp only [rot02Matrix, Matrix.mulVec] <;>
    rw [Matrix.vec3_dotProduct] <;>
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Matrix.vecEmpty] <;>
    ring

set_option maxHeartbeats 2000000 in
/-- The `12`-rotation matrix acts by the explicit rotation formula. -/
theorem rot12Matrix_apply (θ : ℝ) (x : Fin 3 → ℝ) :
    Matrix.mulVec (rot12Matrix θ) x
      = ![x 0, Real.cos θ * x 1 - Real.sin θ * x 2,
          Real.sin θ * x 1 + Real.cos θ * x 2] := by
  funext i
  fin_cases i <;>
    simp only [rot12Matrix, Matrix.mulVec] <;>
    rw [Matrix.vec3_dotProduct] <;>
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Matrix.vecEmpty] <;>
    ring

/-- The `01`-rotation as a `ContinuousLinearMap` is the explicit formula. -/
theorem rot01CLM_apply (θ : ℝ) (x : Fin 3 → ℝ) :
    rot01CLM θ x = ![Real.cos θ * x 0 - Real.sin θ * x 1,
                    Real.sin θ * x 0 + Real.cos θ * x 1, x 2] :=
  rot01Matrix_apply θ x

/-- The `02`-rotation as a `ContinuousLinearMap` is the explicit formula. -/
theorem rot02CLM_apply (θ : ℝ) (x : Fin 3 → ℝ) :
    rot02CLM θ x = ![Real.cos θ * x 0 - Real.sin θ * x 2, x 1,
                    Real.sin θ * x 0 + Real.cos θ * x 2] :=
  rot02Matrix_apply θ x

/-- The `12`-rotation as a `ContinuousLinearMap` is the explicit formula. -/
theorem rot12CLM_apply (θ : ℝ) (x : Fin 3 → ℝ) :
    rot12CLM θ x = ![x 0, Real.cos θ * x 1 - Real.sin θ * x 2,
                    Real.sin θ * x 1 + Real.cos θ * x 2] :=
  rot12Matrix_apply θ x

set_option maxHeartbeats 2000000 in
/-- The `01`-rotation preserves the Euclidean inner product on `Space3`. -/
theorem ip_rot01 (θ : ℝ) (x y : Fin 3 → ℝ) :
    (∑ i, (rot01CLM θ x) i * (rot01CLM θ y) i) = ∑ i, x i * y i := by
  rw [rot01CLM_apply, rot01CLM_apply]
  simp only [Fin.sum_univ_three]
  norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.vecEmpty]
  linear_combination (x 0 * y 0 + x 1 * y 1) * Real.cos_sq_add_sin_sq θ

set_option maxHeartbeats 2000000 in
/-- The `02`-rotation preserves the Euclidean inner product on `Space3`. -/
theorem ip_rot02 (θ : ℝ) (x y : Fin 3 → ℝ) :
    (∑ i, (rot02CLM θ x) i * (rot02CLM θ y) i) = ∑ i, x i * y i := by
  rw [rot02CLM_apply, rot02CLM_apply]
  simp only [Fin.sum_univ_three]
  norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.vecEmpty]
  linear_combination (x 0 * y 0 + x 2 * y 2) * Real.cos_sq_add_sin_sq θ

set_option maxHeartbeats 2000000 in
/-- The `12`-rotation preserves the Euclidean inner product on `Space3`. -/
theorem ip_rot12 (θ : ℝ) (x y : Fin 3 → ℝ) :
    (∑ i, (rot12CLM θ x) i * (rot12CLM θ y) i) = ∑ i, x i * y i := by
  rw [rot12CLM_apply, rot12CLM_apply]
  simp only [Fin.sum_univ_three]
  norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.vecEmpty]
  linear_combination (x 1 * y 1 + x 2 * y 2) * Real.cos_sq_add_sin_sq θ


/-- The threefold composite rotation preserves the Euclidean inner product.

The three single-rotation facts are composed: the `01`-rotation first, then the `02`- and
`12`-rotations applied to its output. -/
theorem ip_threefold (θ1 θ2 θ3 : ℝ) (t : ℝ) (x y : Fin 3 → ℝ) :
    (∑ i, (((rot12CLM (t * θ3)).comp (rot02CLM (t * θ2))).comp (rot01CLM (t * θ1)) x) i
        * (((rot12CLM (t * θ3)).comp (rot02CLM (t * θ2))).comp (rot01CLM (t * θ1)) y) i)
      = ∑ i, x i * y i := by
  have h1 : (∑ i, (rot01CLM (t * θ1) x) i * (rot01CLM (t * θ1) y) i) = ∑ i, x i * y i :=
    ip_rot01 (t * θ1) x y
  have h2 : (∑ i, (rot02CLM (t * θ2) (rot01CLM (t * θ1) x)) i
      * (rot02CLM (t * θ2) (rot01CLM (t * θ1) y)) i) = ∑ i, x i * y i := by
    rw [← h1]
    exact ip_rot02 (t * θ2) _ _
  have h3 : (∑ i, (rot12CLM (t * θ3) (rot02CLM (t * θ2) (rot01CLM (t * θ1) x))) i
      * (rot12CLM (t * θ3) (rot02CLM (t * θ2) (rot01CLM (t * θ1) y))) i)
      = ∑ i, x i * y i := by
    rw [← h2]
    exact ip_rot12 (t * θ3) _ _
  simpa only [ContinuousLinearMap.comp_apply] using h3

/-- The threefold composite of the coordinate-plane rotations preserves the Euclidean
inner product, so it is an admissible `A` in the roundness lemmas. -/
theorem solution (t θ1 θ2 θ3 : ℝ) (x y : (Fin 3 → ℝ)) :
    (∑ i, (((rot12CLM (t * θ3)).comp (rot02CLM (t * θ2))).comp (rot01CLM (t * θ1)) x) i
        * (((rot12CLM (t * θ3)).comp (rot02CLM (t * θ2))).comp (rot01CLM (t * θ1)) y) i)
      = ∑ i, x i * y i := by
  have h1 : (∑ i, (rot01CLM (t * θ1) x) i * (rot01CLM (t * θ1) y) i) = ∑ i, x i * y i :=
    ip_rot01 (t * θ1) x y
  have h2 : (∑ i, (rot02CLM (t * θ2) (rot01CLM (t * θ1) x)) i
      * (rot02CLM (t * θ2) (rot01CLM (t * θ1) y)) i) = ∑ i, x i * y i := by
    rw [← h1]
    exact ip_rot02 (t * θ2) _ _
  have h3 : (∑ i, (rot12CLM (t * θ3) (rot02CLM (t * θ2) (rot01CLM (t * θ1) x))) i
      * (rot12CLM (t * θ3) (rot02CLM (t * θ2) (rot01CLM (t * θ1) y))) i)
      = ∑ i, x i * y i := by
    rw [← h2]
    exact ip_rot12 (t * θ3) _ _
  simpa only [ContinuousLinearMap.comp_apply] using h3
