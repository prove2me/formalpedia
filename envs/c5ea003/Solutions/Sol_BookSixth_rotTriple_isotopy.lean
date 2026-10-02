-- Prove2me | solution 1 for BookSixth.rotTriple_isotopy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T05:45:51.414396+00:00
-- url     : https://prove2.me/submissions/b6c7d2af-7798-42a7-ae2b-741b131b1628

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthRotations3
import Definitions.Def_BookSixthRotTriple
import Theorems.Thm_BookSixth_rotTriple_is_continuous_linear_equiv
open BookSixth
open Matrix
open scoped Matrix
noncomputable section

def isoR (t θ1 θ2 θ3 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  rot12Matrix (t * θ3) * rot02Matrix (t * θ2) * rot01Matrix (t * θ1)

def isoE (θ1 θ2 θ3 t : ℝ) : Space3 ≃SL[RingHom.id ℝ] Space3 :=
  (rotTriple_is_continuous_linear_equiv θ1 θ2 θ3 t).choose

lemma rotTriple_zero (θ1 θ2 θ3 : ℝ) (x : Space3) : rotTriple 0 θ1 θ2 θ3 x = x := by
  have h01 : rot01Matrix 0 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [rot01Matrix]
  have h02 : rot02Matrix 0 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [rot02Matrix]
  have h12 : rot12Matrix 0 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [rot12Matrix]
  simp [rotTriple, h01, h02, h12, rot12CLM, rot02CLM, rot01CLM]

def isoH (θ1 θ2 θ3 : ℝ) (a : Space3) (t : ℝ) : Space3 ≃ₜ Space3 :=
  (isoE θ1 θ2 θ3 t).toHomeomorph.trans (Homeomorph.vadd (t • a))

lemma isoH_apply (θ1 θ2 θ3 t : ℝ) (a x : Space3) :
    isoH θ1 θ2 θ3 a t x = rotTriple t θ1 θ2 θ3 x + t • a := by
  simp only [isoH, Homeomorph.trans_apply, Homeomorph.vadd_apply,
    ContinuousLinearEquiv.coe_toHomeomorph]
  show t • a + isoE θ1 θ2 θ3 t x = _
  rw [show isoE θ1 θ2 θ3 t x = rotTriple t θ1 θ2 θ3 x from
    (rotTriple_is_continuous_linear_equiv θ1 θ2 θ3 t).choose_spec.1 x]
  abel

lemma isoH_symm_apply (θ1 θ2 θ3 t : ℝ) (a y : Space3) :
    (isoH θ1 θ2 θ3 a t).symm y
      = (isoR t θ1 θ2 θ3)ᵀ *ᵥ y - t • ((isoR t θ1 θ2 θ3)ᵀ *ᵥ a) := by
  have key : (isoH θ1 θ2 θ3 a t).symm y = (isoE θ1 θ2 θ3 t).symm (y - t • a) := by
    simp only [isoH, Homeomorph.symm_trans_apply,
      ContinuousLinearEquiv.coe_symm_toHomeomorph]
    unfold Homeomorph.vadd
    simp
    abel
  rw [key]
  rw [show (isoE θ1 θ2 θ3 t).symm = fun x =>
      (isoR t θ1 θ2 θ3)ᵀ *ᵥ x by
    funext x
    exact (rotTriple_is_continuous_linear_equiv θ1 θ2 θ3 t).choose_spec.2 x]
  simp [Matrix.mulVec_sub, Matrix.mulVec_smul]

theorem solution (θ1 θ2 θ3 : ℝ) (a : Space3) :
    ∃ H : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => H p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧
      (∀ t x, H t x = rotTriple t θ1 θ2 θ3 x + t • a) := by
  have hR : Continuous fun t : ℝ => isoR t θ1 θ2 θ3 := by
    unfold isoR rot12Matrix rot02Matrix rot01Matrix
    fun_prop
  have hfwd : Continuous fun p : ℝ × Space3 => rotTriple p.1 θ1 θ2 θ3 p.2 + p.1 • a := by
    have key : (fun p : ℝ × Space3 => rotTriple p.1 θ1 θ2 θ3 p.2 + p.1 • a)
        = (fun p => isoR p.1 θ1 θ2 θ3 *ᵥ p.2 + p.1 • a) := by
      funext p
      unfold rotTriple isoR
      simp only [rot12CLM, rot02CLM, rot01CLM]
      simp
      simp only [Matrix.mul_assoc]
    rw [key]
    unfold isoR rot12Matrix rot02Matrix rot01Matrix
    fun_prop
  have hsymm : Continuous fun p : ℝ × Space3 =>
      (isoR p.1 θ1 θ2 θ3)ᵀ *ᵥ p.2 - p.1 • ((isoR p.1 θ1 θ2 θ3)ᵀ *ᵥ a) := by
    fun_prop
  refine ⟨fun t => isoH θ1 θ2 θ3 a t, ?_, ?_, ?_, ?_⟩
  · show Continuous fun p : ℝ × Space3 => (isoH θ1 θ2 θ3 a p.1) p.2
    rw [show (fun p : ℝ × Space3 => (isoH θ1 θ2 θ3 a p.1) p.2)
        = (fun p => rotTriple p.1 θ1 θ2 θ3 p.2 + p.1 • a) by
      funext p; exact isoH_apply θ1 θ2 θ3 p.1 a p.2]
    exact hfwd
  · show Continuous fun p : ℝ × Space3 => (isoH θ1 θ2 θ3 a p.1).symm p.2
    rw [show (fun p : ℝ × Space3 => (isoH θ1 θ2 θ3 a p.1).symm p.2)
        = (fun p => (isoR p.1 θ1 θ2 θ3)ᵀ *ᵥ p.2
            - p.1 • ((isoR p.1 θ1 θ2 θ3)ᵀ *ᵥ a)) by
      funext p; exact isoH_symm_apply θ1 θ2 θ3 p.1 a p.2]
    exact hsymm
  · intro x
    show isoH θ1 θ2 θ3 a 0 x = x
    rw [isoH_apply, rotTriple_zero]
    simp
  · intro t x
    show isoH θ1 θ2 θ3 a t x = rotTriple t θ1 θ2 θ3 x + t • a
    exact isoH_apply θ1 θ2 θ3 t a x
