-- Prove2me | solution 1 for BookSixth.rotTriple_is_continuous_linear_equiv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T01:34:23.179745+00:00
-- url     : https://prove2.me/submissions/e3cd3b43-cea0-4f46-89b9-564904e08199

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthRotations3
import Definitions.Def_BookSixthRotTriple
open scoped BigOperators
open scoped Matrix
open BookSixth Matrix

noncomputable section

lemma rot01_transpose_mul (θ : ℝ) : (rot01Matrix θ)ᵀ * rot01Matrix θ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot01Matrix, Matrix.mul_apply,
    Fin.sum_univ_three, Matrix.transpose_apply] <;> ring_nf <;>
    nlinarith [Real.cos_sq_add_sin_sq θ]
lemma rot02_transpose_mul (θ : ℝ) : (rot02Matrix θ)ᵀ * rot02Matrix θ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot02Matrix, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;>
    ring_nf <;> nlinarith [Real.cos_sq_add_sin_sq θ]
lemma rot12_transpose_mul (θ : ℝ) : (rot12Matrix θ)ᵀ * rot12Matrix θ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot12Matrix, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;>
    ring_nf <;> nlinarith [Real.cos_sq_add_sin_sq θ]

lemma trans_mul_trans {A B : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : Aᵀ * A = 1) (hB : Bᵀ * B = 1) : (A * B)ᵀ * (A * B) = 1 := by
  rw [transpose_mul]
  calc Bᵀ * Aᵀ * (A * B) = Bᵀ * ((Aᵀ * A) * B) := by
        simp only [Matrix.mul_assoc]
    _ = Bᵀ * B := by rw [hA, Matrix.one_mul]
    _ = 1 := hB

lemma trans_mul_trans3 {A B C : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : Aᵀ * A = 1) (hB : Bᵀ * B = 1) (hC : Cᵀ * C = 1) :
    (A * B * C)ᵀ * (A * B * C) = 1 := by
  have hAB : (A * B)ᵀ * (A * B) = 1 := trans_mul_trans hA hB
  rw [show A * B * C = (A * B) * C by simp only [Matrix.mul_assoc],
    transpose_mul]
  calc Cᵀ * (A * B)ᵀ * ((A * B) * C) = Cᵀ * ((A * B)ᵀ * (A * B)) * C := by
        simp only [Matrix.mul_assoc]
    _ = Cᵀ * C := by rw [hAB, Matrix.mul_one]
    _ = 1 := hC

-- the composite
lemma rotM_transpose_mul (t θ1 θ2 θ3 : ℝ) :
    (rot12Matrix (t * θ3) * rot02Matrix (t * θ2) * rot01Matrix (t * θ1))ᵀ *
      (rot12Matrix (t * θ3) * rot02Matrix (t * θ2) * rot01Matrix (t * θ1)) = 1 := by
  have hAB : (rot12Matrix (t * θ3) * rot02Matrix (t * θ2))ᵀ *
      (rot12Matrix (t * θ3) * rot02Matrix (t * θ2)) = 1 :=
    trans_mul_trans (rot12_transpose_mul _) (rot02_transpose_mul _)
  exact trans_mul_trans hAB (rot01_transpose_mul _)

def rotM (t θ1 θ2 θ3 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  rot12Matrix (t * θ3) * rot02Matrix (t * θ2) * rot01Matrix (t * θ1)

lemma leftInv_mulVec (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : Aᵀ * A = 1) (x : Fin 3 → ℝ) :
    Aᵀ *ᵥ (A *ᵥ x) = x := by
  calc Aᵀ *ᵥ (A *ᵥ x) = (Aᵀ * A) *ᵥ x := by
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
    _ = x := by rw [hA, Matrix.one_mulVec]

lemma rotM_inj (t θ1 θ2 θ3 : ℝ) : Function.Injective (rotM t θ1 θ2 θ3).mulVec := by
  intro u v h
  have h2 : (rotM t θ1 θ2 θ3)ᵀ *ᵥ ((rotM t θ1 θ2 θ3) *ᵥ u)
      = (rotM t θ1 θ2 θ3)ᵀ *ᵥ ((rotM t θ1 θ2 θ3) *ᵥ v) :=
    congrArg (fun w : Fin 3 → ℝ => (rotM t θ1 θ2 θ3)ᵀ *ᵥ w) h
  unfold rotM at h2
  rw [leftInv_mulVec _ (rotM_transpose_mul _ _ _ _) u,
      leftInv_mulVec _ (rotM_transpose_mul _ _ _ _) v] at h2
  exact h2


abbrev RR := RingHom.id ℝ

def rotCLE (t θ1 θ2 θ3 : ℝ) : (Fin 3 → ℝ) ≃SL[RR] (Fin 3 → ℝ) := by
  let hclm : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
    { toLinearMap := (rotM t θ1 θ2 θ3).mulVecLin
      cont := (rotM t θ1 θ2 θ3).mulVecLin.continuous_of_finiteDimensional }
  have hinj' : Function.Injective ⇑hclm := by
    intro x y hxy
    have : (rotM t θ1 θ2 θ3).mulVec x = (rotM t θ1 θ2 θ3).mulVec y := by
      simpa only [hclm, ContinuousLinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.coe_mk, Matrix.mulVecLin_apply] using hxy
    exact rotM_inj t θ1 θ2 θ3 this
  refine ContinuousLinearEquiv.ofBijective hclm (LinearMap.ker_eq_bot.mpr hinj') ?_
  exact LinearMap.range_eq_top.2
    ((LinearMap.injective_iff_surjective
      (f := (hclm : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)))).mp hinj')

-- ### Step 0.  For a square matrix, `Aᵀ * A = 1` also gives `A * Aᵀ = 1`. `Aᵀ * A = 1` implies `A`, hence `Aᵀ`, is a unit; cancelling the unit `A` on the left of `A * Aᵀ * A = 1 * A` then yields the claim.
lemma transpose_mul_to_mul_transpose (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : Aᵀ * A = 1) :
    A * Aᵀ = 1 := by
  have hdetA : IsUnit A.det := by
    rw [isUnit_iff_ne_zero]
    intro h
    have h2 := congrArg Matrix.det hA
    rw [Matrix.det_mul, Matrix.det_transpose, h, Matrix.det_one] at h2
    simp at h2
  have hunitA : IsUnit A := Matrix.isUnit_iff_isUnit_det A |>.mpr hdetA
  have key : A * Aᵀ * A = 1 * A := by
    calc A * Aᵀ * A = A * (Aᵀ * A) := Matrix.mul_assoc A Aᵀ A
      _ = A * 1 := by rw [hA]
      _ = A := Matrix.mul_one _
      _ = 1 * A := (Matrix.one_mul _).symm
  rw [hunitA.mul_left_inj.mp key]

-- ### Step 1.  The transpose is a pre-image of the forward map. `rotCLE` is built from `(rotM _).mulVecLin`, so applying it is *definitionally* `rotM.mulVec`; this is what `change` records.
lemma rotM_transpose_mulVec (t θ1 θ2 θ3 : ℝ) (x : Fin 3 → ℝ) :
    rotCLE t θ1 θ2 θ3 ((rotM t θ1 θ2 θ3)ᵀ *ᵥ x) = x := by
  change (rotM t θ1 θ2 θ3).mulVecLin ((rotM t θ1 θ2 θ3)ᵀ *ᵥ x) = x
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  unfold rotM
  rw [transpose_mul_to_mul_transpose _ (rotM_transpose_mul t θ1 θ2 θ3),
    Matrix.one_mulVec]

-- ### The target lemma. `ContinuousLinearEquiv.injective` turns the goal into a statement about the forward map, which Step 1 settles.
lemma rotCLE_symm_apply (t θ1 θ2 θ3 : ℝ) (x : Fin 3 → ℝ) :
    (rotCLE t θ1 θ2 θ3).symm x = (rotM t θ1 θ2 θ3)ᵀ *ᵥ x := by
  refine ContinuousLinearEquiv.injective (rotCLE t θ1 θ2 θ3) ?_
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact (rotM_transpose_mulVec t θ1 θ2 θ3 x).symm

-- The inverse of the threefold rotation at time t is the transpose of its matrix.  This is what makes the inverse leg of the isotopy expressible as a transpose: (H t)^{-1} y = R(t)^T y - t (R(t)^T a).

-- The threefold rotation at time t is a continuous linear equivalence whose inverse is the transpose of its matrix.  This is what makes the inverse leg of the isotopy explicit: (H t)^{-1} y = R(t)^T y - t (R(t)^T a).

-- `rotCLE` applied is the rotation matrix applied, definitionally.
lemma rotCLE_eq_mulVec (t θ1 θ2 θ3 : ℝ) (w : Fin 3 → ℝ) :
    rotCLE t θ1 θ2 θ3 w = rotM t θ1 θ2 θ3 *ᵥ w := rfl

theorem solution (θ1 θ2 θ3 t : ℝ) :
    ∃ E : (Fin 3 → ℝ) ≃SL[RingHom.id ℝ] (Fin 3 → ℝ),
      (∀ x, E x = rotTriple t θ1 θ2 θ3 x) ∧
      (∀ x, E.symm x
        = (rot12Matrix (t * θ3) * rot02Matrix (t * θ2)
            * rot01Matrix (t * θ1))ᵀ *ᵥ x) := by
  refine ⟨rotCLE t θ1 θ2 θ3, fun x => ?_,
    fun x => ?_⟩
  · show (rotM t θ1 θ2 θ3) *ᵥ x = rotTriple t θ1 θ2 θ3 x
    unfold rotM
    unfold rotTriple
    simp only [rot12CLM, rot02CLM, rot01CLM]
    simp
    simp only [Matrix.mul_assoc]
  · rw [rotCLE_symm_apply]
    rfl
