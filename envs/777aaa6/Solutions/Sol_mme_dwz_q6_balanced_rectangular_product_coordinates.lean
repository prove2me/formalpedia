-- Prove2me | solution 1 for mme_dwz_q6_balanced_rectangular_product_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T08:57:12.689405+00:00
-- url     : https://prove2.me/submissions/b24194ef-2656-4d91-9d98-2412b9af2ba7

import Definitions.Def_mme_dwz_component_word_projection
import Mathlib.Tactic

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZBalancedRectangular

private def rectO : Fin 8 := 0
private def rectM (i : Fin 6) : Fin 8 := ⟨i.val + 1, by omega⟩
private def rectT : Fin 8 := 7

private theorem rectM_injective : Function.Injective rectM := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [rectM] at this
  omega

private theorem gradeThree_left (i : Fin 6) :
    cwSquarePairGrade 6 (rectT, rectM i) = 3 := by
  have hiT : i.val + 1 ≠ 7 := by omega
  simp [cwSquarePairGrade, cwSquareCoordGrade, rectT, rectM, hiT]

private theorem gradeThree_right (i : Fin 6) :
    cwSquarePairGrade 6 (rectM i, rectT) = 3 := by
  have hiT : i.val + 1 ≠ 7 := by omega
  simp [cwSquarePairGrade, cwSquareCoordGrade, rectT, rectM, hiT]

private theorem gradeOne_left (i : Fin 6) :
    cwSquarePairGrade 6 (rectO, rectM i) = 1 := by
  have hiT : i.val + 1 ≠ 7 := by omega
  simp [cwSquarePairGrade, cwSquareCoordGrade, rectO, rectM, hiT]

private theorem gradeOne_right (i : Fin 6) :
    cwSquarePairGrade 6 (rectM i, rectO) = 1 := by
  have hiT : i.val + 1 ≠ 7 := by omega
  simp [cwSquarePairGrade, cwSquareCoordGrade, rectO, rectM, hiT]

private def gradeThreeEncode : Fin 6 ⊕ Fin 6 → CoarsePair 6 3
  | Sum.inl i => ⟨(rectT, rectM i), gradeThree_left i⟩
  | Sum.inr i => ⟨(rectM i, rectT), gradeThree_right i⟩

private def gradeThreeDecode (p : CoarsePair 6 3) : Fin 6 ⊕ Fin 6 :=
  if p.1.1.val = 7 then
    Sum.inl (Fin.ofNat 6 (p.1.2.val - 1))
  else
    Sum.inr (Fin.ofNat 6 (p.1.1.val - 1))

private theorem gradeThreeDecode_encode :
    Function.LeftInverse gradeThreeDecode gradeThreeEncode := by
  intro c
  rcases c with i | i <;> fin_cases i <;> rfl

private theorem gradeThreeEncode_decode :
    Function.RightInverse gradeThreeDecode gradeThreeEncode := by
  rintro ⟨⟨a, b⟩, hp⟩
  apply Subtype.ext
  fin_cases a <;> fin_cases b <;>
    simp [gradeThreeDecode, gradeThreeEncode, cwSquarePairGrade,
      cwSquareCoordGrade, rectM, rectT] at hp ⊢

noncomputable def gradeThreeChannelEquiv :
    CoarsePair 6 3 ≃ (Fin 6 ⊕ Fin 6) where
  toFun := gradeThreeDecode
  invFun := gradeThreeEncode
  left_inv := gradeThreeEncode_decode
  right_inv := gradeThreeDecode_encode

private def gradeOneEncode : Fin 6 ⊕ Fin 6 → CoarsePair 6 1
  | Sum.inl i => ⟨(rectO, rectM i), gradeOne_left i⟩
  | Sum.inr i => ⟨(rectM i, rectO), gradeOne_right i⟩

private def gradeOneDecode (p : CoarsePair 6 1) : Fin 6 ⊕ Fin 6 :=
  if p.1.1.val = 0 then
    Sum.inl (Fin.ofNat 6 (p.1.2.val - 1))
  else
    Sum.inr (Fin.ofNat 6 (p.1.1.val - 1))

private theorem gradeOneDecode_encode :
    Function.LeftInverse gradeOneDecode gradeOneEncode := by
  intro c
  rcases c with i | i <;> fin_cases i <;> rfl

private theorem gradeOneEncode_decode :
    Function.RightInverse gradeOneDecode gradeOneEncode := by
  rintro ⟨⟨a, b⟩, hp⟩
  apply Subtype.ext
  fin_cases a <;> fin_cases b <;>
    simp [gradeOneDecode, gradeOneEncode, cwSquarePairGrade,
      cwSquareCoordGrade, rectM, rectO] at hp ⊢

noncomputable def gradeOneChannelEquiv :
    CoarsePair 6 1 ≃ (Fin 6 ⊕ Fin 6) where
  toFun := gradeOneDecode
  invFun := gradeOneEncode
  left_inv := gradeOneEncode_decode
  right_inv := gradeOneDecode_encode

noncomputable def gradeThreeCoordinate :
    LiftedCoarsePair.{u} 6 3 ≃ Fin 12 :=
  Equiv.ulift.trans <|
    gradeThreeChannelEquiv.trans <|
      finSumFinEquiv.trans (finCongr (by omega))

noncomputable def gradeOneCoordinate :
    LiftedCoarsePair.{u} 6 1 ≃ Fin 12 :=
  Equiv.ulift.trans <|
    gradeOneChannelEquiv.trans <|
      finSumFinEquiv.trans (finCongr (by omega))

theorem gradeThreeCoordinate_source (p : LiftedCoarsePair.{u} 6 3) :
    p.down.1 =
      match (finSumFinEquiv.symm (gradeThreeCoordinate p) : Fin 6 ⊕ Fin 6) with
      | Sum.inl i => (rectT, rectM i)
      | Sum.inr i => (rectM i, rectT) := by
  have h := gradeThreeChannelEquiv.symm_apply_apply p.down
  change p.down.1 = _
  rw [show finSumFinEquiv.symm (gradeThreeCoordinate p) =
      gradeThreeChannelEquiv p.down from by
    apply finSumFinEquiv.injective
    rw [finSumFinEquiv.apply_symm_apply]
    rfl]
  generalize hc : gradeThreeChannelEquiv p.down = c at h ⊢
  rcases c with i | i <;>
    simpa [gradeThreeChannelEquiv, gradeThreeEncode] using
      congrArg Subtype.val h.symm

theorem gradeOneCoordinate_source (p : LiftedCoarsePair.{u} 6 1) :
    p.down.1 =
      match (finSumFinEquiv.symm (gradeOneCoordinate p) : Fin 6 ⊕ Fin 6) with
      | Sum.inl i => (rectO, rectM i)
      | Sum.inr i => (rectM i, rectO) := by
  have h := gradeOneChannelEquiv.symm_apply_apply p.down
  change p.down.1 = _
  rw [show finSumFinEquiv.symm (gradeOneCoordinate p) =
      gradeOneChannelEquiv p.down from by
    apply finSumFinEquiv.injective
    rw [finSumFinEquiv.apply_symm_apply]
    rfl]
  generalize hc : gradeOneChannelEquiv p.down = c at h ⊢
  rcases c with i | i <;>
    simpa [gradeOneChannelEquiv, gradeOneEncode] using
      congrArg Subtype.val h.symm

private def sumSixProductEquiv : (Fin 6 ⊕ Fin 6) ≃ Fin 2 × Fin 6 where
  toFun
    | Sum.inl i => (0, i)
    | Sum.inr i => (1, i)
  invFun p := if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
  left_inv c := by
    rcases c with i | i <;> rfl
  right_inv p := by
    rcases p with ⟨b, i⟩
    fin_cases b <;> rfl

/-- Product coordinates for the twelve grade-three q=6 channels. -/
noncomputable def gradeThreeProductEquiv :
    LiftedCoarsePair.{u} 6 3 ≃ Fin 2 × Fin 6 :=
  Equiv.ulift.trans (gradeThreeChannelEquiv.trans sumSixProductEquiv)

/-- Product coordinates for the twelve grade-one q=6 channels. -/
noncomputable def gradeOneProductEquiv :
    LiftedCoarsePair.{u} 6 1 ≃ Fin 2 × Fin 6 :=
  Equiv.ulift.trans (gradeOneChannelEquiv.trans sumSixProductEquiv)

theorem gradeThreeProductEquiv_leftGrade
    (p : LiftedCoarsePair.{u} 6 3) :
    p.leftGrade = ![2, 1] (gradeThreeProductEquiv p).1 := by
  have h := gradeThreeChannelEquiv.symm_apply_apply p.down
  generalize hc : gradeThreeChannelEquiv p.down = c at h ⊢
  rcases c with i | i
  · have hfirst : (gradeThreeProductEquiv p).1 = 0 := by
      change (sumSixProductEquiv (gradeThreeChannelEquiv p.down)).1 = 0
      rw [hc]
      rfl
    rw [hfirst]
    change p.down.leftGrade = 2
    rw [← h]
    rfl
  · have hfirst : (gradeThreeProductEquiv p).1 = 1 := by
      change (sumSixProductEquiv (gradeThreeChannelEquiv p.down)).1 = 1
      rw [hc]
      rfl
    rw [hfirst]
    change p.down.leftGrade = 1
    rw [← h]
    have hi : i.val ≠ 6 := by omega
    simp [gradeThreeChannelEquiv, gradeThreeEncode, CoarsePair.leftGrade,
      cwSquareCoordGrade, rectM, hi]

theorem gradeOneProductEquiv_leftGrade
    (p : LiftedCoarsePair.{u} 6 1) :
    p.leftGrade = ![0, 1] (gradeOneProductEquiv p).1 := by
  have h := gradeOneChannelEquiv.symm_apply_apply p.down
  generalize hc : gradeOneChannelEquiv p.down = c at h ⊢
  rcases c with i | i
  · have hfirst : (gradeOneProductEquiv p).1 = 0 := by
      change (sumSixProductEquiv (gradeOneChannelEquiv p.down)).1 = 0
      rw [hc]
      rfl
    rw [hfirst]
    change p.down.leftGrade = 0
    rw [← h]
    rfl
  · have hfirst : (gradeOneProductEquiv p).1 = 1 := by
      change (sumSixProductEquiv (gradeOneChannelEquiv p.down)).1 = 1
      rw [hc]
      rfl
    rw [hfirst]
    change p.down.leftGrade = 1
    rw [← h]
    have hi : i.val ≠ 6 := by omega
    simp [gradeOneChannelEquiv, gradeOneEncode, CoarsePair.leftGrade,
      cwSquareCoordGrade, rectM, hi]

end MME.DWZBalancedRectangular

/-- The q=6 grade-three and grade-one rectangular alphabets are two equal
six-letter fibers, with the displayed relation to the canonical left grade. -/
theorem mme_dwz_q6_balanced_rectangular_product_coordinates :
    (∃ e3 : MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6 3 ≃
        Fin 2 × Fin 6,
      ∀ p, p.leftGrade = ![2, 1] (e3 p).1) ∧
    (∃ e1 : MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6 1 ≃
        Fin 2 × Fin 6,
      ∀ p, p.leftGrade = ![0, 1] (e1 p).1) := by
  exact
    ⟨⟨MME.DWZBalancedRectangular.gradeThreeProductEquiv,
        MME.DWZBalancedRectangular.gradeThreeProductEquiv_leftGrade⟩,
      ⟨MME.DWZBalancedRectangular.gradeOneProductEquiv,
        MME.DWZBalancedRectangular.gradeOneProductEquiv_leftGrade⟩⟩

theorem solution :
    (∃ e3 : MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6 3 ≃
        Fin 2 × Fin 6,
      ∀ p, p.leftGrade = ![2, 1] (e3 p).1) ∧
    (∃ e1 : MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6 1 ≃
        Fin 2 × Fin 6,
      ∀ p, p.leftGrade = ![0, 1] (e1 p).1) :=
  mme_dwz_q6_balanced_rectangular_product_coordinates
