-- Prove2me | solution 1 for mme_dwz_table2_automatic_elementary_rows_one_MM_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T06:03:38.699208+00:00
-- url     : https://prove2.me/submissions/2dd75d9f-1d41-4570-953a-ee62db6e03f3

import Mathlib.Tactic
import Definitions.Def_mme_dwz_component_word_projection
import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes
import Theorems.Thm_mme_CW_square_canonical_elementary_blocks
import Theorems.Thm_mme_restrict_kronPow
import Theorems.Thm_mme_kronFin_MMObj_iso

open MME Module PiTensorProduct BigOperators
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZElementaryAutomatic

theorem basisZAllowedSubtensor_restrict_of_all
    {K : Type u} [Field K]
    (T : TensorObj K 3) {ι : Type u}
    (bZ : Basis ι K (T.V 2)) (allowed : ι → Prop)
    [DecidablePred allowed] (hall : ∀ j, allowed j) :
    TensorObj.Restrict T (T.basisZAllowedSubtensor bZ allowed) := by
  let f : ∀ i, T.V i →ₗ[K] T.V i := fun _ ↦ LinearMap.id
  apply mme_restrict_basisZAllowedSubtensor_of_vanishes T T bZ allowed f
  · change PiTensorProduct.map (fun _ : Fin 3 ↦ LinearMap.id) T.t = T.t
    rw [PiTensorProduct.map_id]
    rfl
  · intro j hj
    exact False.elim (hj (hall j))

theorem liftedCoarsePair_grade_zero_leftGrade
    (p : LiftedCoarsePair.{u} 6 (0 : Fin 5)) :
    p.leftGrade = 0 := by
  apply Fin.ext
  change (cwSquareCoordGrade 6 p.down.1.1).val = 0
  have hp := p.down.2
  change cwSquarePairGrade 6 p.down.1 = 0 at hp
  apply congrArg Fin.val at hp
  simp only [cwSquarePairGrade] at hp
  omega

theorem liftedCoarsePair_grade_four_leftGrade
    (p : LiftedCoarsePair.{u} 6 (4 : Fin 5)) :
    p.leftGrade = 2 := by
  apply Fin.ext
  change (cwSquareCoordGrade 6 p.down.1.1).val = 2
  have hp := p.down.2
  change cwSquarePairGrade 6 p.down.1 = 4 at hp
  apply congrArg Fin.val at hp
  simp only [cwSquarePairGrade] at hp
  have hle : (cwSquareCoordGrade 6 p.down.1.2).val ≤ 2 :=
    Nat.le_of_lt_succ (Fin.isLt _)
  omega

theorem card_positions_of_constant
    {n : ℕ} (f : Fin n → Fin 3) (g a : Fin 3)
    (hall : ∀ r, f r = g) :
    Fintype.card {r : Fin n // f r = a} = if a = g then n else 0 := by
  classical
  by_cases h : a = g
  · subst a
    rw [if_pos rfl]
    let e : {r : Fin n // f r = g} ≃ Fin n :=
      { toFun := Subtype.val
        invFun := fun r ↦ ⟨r, hall r⟩
        left_inv := fun r ↦ Subtype.ext rfl
        right_inv := fun _ ↦ rfl }
    simpa only [Fintype.card_fin] using Fintype.card_congr e
  · rw [if_neg h, Fintype.card_eq_zero_iff]
    exact ⟨fun r ↦ h (r.2.symm.trans (hall r.1))⟩

theorem constant_grade_word_allowed
    (s : Fin 15) (m : ℕ) (g : Fin 3)
    (hletter : ∀ p : LiftedCoarsePair.{u} 6
      (MME.DWZSquare.shapeZ s), p.leftGrade = g)
    (hsplit : ∀ a : Fin 3,
      MME.DWZTable2Counts.split s a =
        if a = g then MME.DWZTable2Counts.component s else 0)
    (w : PowIndex (LiftedCoarsePair.{u} 6
      (MME.DWZSquare.shapeZ s))
      (MME.DWZTable2Counts.component s * m)) :
    componentWordAllowed s m w := by
  intro a
  rw [card_positions_of_constant
    (fun r ↦ (PowIndex.get _ w r).leftGrade) g a
    (fun r ↦ hletter (PowIndex.get _ w r)), hsplit]
  by_cases h : a = g <;> simp [h]

theorem row1_word_allowed (m : ℕ)
    (w : PowIndex (LiftedCoarsePair.{u} 6
      (MME.DWZSquare.shapeZ (1 : Fin 15)))
      (MME.DWZTable2Counts.component (1 : Fin 15) * m)) :
    componentWordAllowed (1 : Fin 15) m w := by
  apply constant_grade_word_allowed 1 m 0
  · intro p
    exact liftedCoarsePair_grade_zero_leftGrade p
  · intro a
    fin_cases a <;> rfl

theorem row2_word_allowed (m : ℕ)
    (w : PowIndex (LiftedCoarsePair.{u} 6
      (MME.DWZSquare.shapeZ (2 : Fin 15)))
      (MME.DWZTable2Counts.component (2 : Fin 15) * m)) :
    componentWordAllowed (2 : Fin 15) m w := by
  apply constant_grade_word_allowed 2 m 0
  · intro p
    exact liftedCoarsePair_grade_zero_leftGrade p
  · intro a
    fin_cases a <;> rfl

theorem row6_word_allowed (m : ℕ)
    (w : PowIndex (LiftedCoarsePair.{u} 6
      (MME.DWZSquare.shapeZ (6 : Fin 15)))
      (MME.DWZTable2Counts.component (6 : Fin 15) * m)) :
    componentWordAllowed (6 : Fin 15) m w := by
  apply constant_grade_word_allowed 6 m 0
  · intro p
    exact liftedCoarsePair_grade_zero_leftGrade p
  · intro a
    fin_cases a <;> rfl

theorem row8_word_allowed (m : ℕ)
    (w : PowIndex (LiftedCoarsePair.{u} 6
      (MME.DWZSquare.shapeZ (8 : Fin 15)))
      (MME.DWZTable2Counts.component (8 : Fin 15) * m)) :
    componentWordAllowed (8 : Fin 15) m w := by
  apply constant_grade_word_allowed 8 m 0
  · intro p
    exact liftedCoarsePair_grade_zero_leftGrade p
  · intro a
    fin_cases a <;> rfl

theorem row11_word_allowed (m : ℕ)
    (w : PowIndex (LiftedCoarsePair.{u} 6
      (MME.DWZSquare.shapeZ (11 : Fin 15)))
      (MME.DWZTable2Counts.component (11 : Fin 15) * m)) :
    componentWordAllowed (11 : Fin 15) m w := by
  apply constant_grade_word_allowed 11 m 0
  · intro p
    exact liftedCoarsePair_grade_zero_leftGrade p
  · intro a
    fin_cases a <;> rfl

theorem gradeFour_row_word_allowed
    (m : ℕ)
    (w : PowIndex (LiftedCoarsePair.{u} 6
      (MME.DWZSquare.shapeZ (0 : Fin 15)))
      (MME.DWZTable2Counts.component (0 : Fin 15) * m)) :
    componentWordAllowed (0 : Fin 15) m w := by
  apply constant_grade_word_allowed 0 m 2
  · intro p
    exact liftedCoarsePair_grade_four_leftGrade p
  · intro a
    fin_cases a <;> rfl

theorem allWords_power_restrict
    {K : Type u} [Field K]
    (s : Fin 15) (m : ℕ)
    (hall : ∀ w : PowIndex (LiftedCoarsePair.{u} 6
      (MME.DWZSquare.shapeZ s))
      (MME.DWZTable2Counts.component s * m),
        componentWordAllowed s m w) :
    TensorObj.Restrict
      ((canonicalComponentBlock K s).kronPow
        (MME.DWZTable2Counts.component s * m))
      (restrictedComponentPower K s m) := by
  letI : DecidablePred (componentWordAllowed s m) := Classical.decPred _
  simpa only [restrictedComponentPower, componentPowerProjectionGrading] using
    (basisZAllowedSubtensor_restrict_of_all
      ((canonicalComponentBlock K s).kronPow
        (MME.DWZTable2Counts.component s * m))
      (componentPowerZBasis K s m) (componentWordAllowed s m) hall)

theorem MMObj_kronPow_iso
    {K : Type u} [Field K] (n a b c : ℕ) :
    TensorObj.Isomorphic
      ((MMObj K a b c).kronPow n)
      (MMObj K (a ^ n) (b ^ n) (c ^ n)) := by
  have heq :
      (MMObj K a b c).kronPow n =
        TensorObj.kronFin n (fun _ ↦ MMObj K a b c) := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [TensorObj.kronPow, TensorObj.kronFin, ih]
  rw [heq]
  have h := mme_kronFin_MMObj_iso (K := K) n
    (fun _ ↦ a) (fun _ ↦ b) (fun _ ↦ c)
  simpa only [Fin.prod_const] using h

theorem automatic_MM_power_restrict
    {K : Type u} [Field K]
    (s : Fin 15) (m a b c : ℕ)
    (hblock : TensorObj.Restrict (MMObj K a b c)
      (canonicalComponentBlock K s))
    (hall : ∀ w : PowIndex (LiftedCoarsePair.{u} 6
      (MME.DWZSquare.shapeZ s))
      (MME.DWZTable2Counts.component s * m),
        componentWordAllowed s m w) :
    TensorObj.Restrict
      (MMObj K (a ^ (MME.DWZTable2Counts.component s * m))
        (b ^ (MME.DWZTable2Counts.component s * m))
        (c ^ (MME.DWZTable2Counts.component s * m)))
      (restrictedComponentPower K s m) := by
  let n := MME.DWZTable2Counts.component s * m
  have hpow := mme_restrict_kronPow hblock n
  have hiso := MMObj_kronPow_iso (K := K) n a b c
  exact TensorObj.Restrict.trans hiso.2
    (TensorObj.Restrict.trans hpow (allWords_power_restrict s m hall))

theorem volume_rpow_identity (d n : ℕ) (tau : ℝ) :
    ((((d : ℝ) ^ tau) ^ n) ^ (6 : ℕ)) =
      (((((d ^ n) ^ 2) * ((d ^ n) ^ 2) *
          ((d ^ n) ^ 2) : ℕ) : ℝ) ^ tau) := by
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg d) tau n]
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg d) (tau * n) 6]
  have hnat : (d ^ n) ^ 2 * (d ^ n) ^ 2 * (d ^ n) ^ 2 =
      d ^ (n * 6) := by ring
  rw [hnat, Nat.cast_pow]
  rw [← Real.rpow_natCast_mul (Nat.cast_nonneg d) (n * 6) tau]
  congr 1
  push_cast
  ring

end MME.DWZElementaryAutomatic

open MME.DWZElementaryAutomatic

theorem solution
    {K : Type u} [Field K] (tau : ℝ)
    (m : ℕ) (s : Fin 15)
    (hs : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 6 ∨ s = 8 ∨ s = 11) :
    ∃ a b c : ℕ,
      TensorObj.Restrict (MMObj K a b c)
        (restrictedComponentPower K s m) ∧
      (((componentBase tau s) ^
          (MME.DWZTable2Counts.component s * m)) ^ (6 : ℕ)) *
          Real.exp (-(0 : ℝ) * Real.sqrt
            (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
        (((((a * b * c) ^ 2) * ((a * b * c) ^ 2) *
              ((a * b * c) ^ 2) : ℕ) : ℝ) ^ tau) := by
  rcases mme_CW_square_canonical_elementary_blocks (K := K) 6 with
    ⟨_, h0, h1, h2, _, _, _, _, h6, h8, _, _, h11⟩
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨1, 1, 1, ?_, ?_⟩
    · have hblock : TensorObj.Restrict (MMObj K 1 1 1)
          (canonicalComponentBlock K (0 : Fin 15)) := by
        simpa [canonicalComponentBlock, shapeX, shapeY, shapeZ] using h0
      simpa only [one_pow] using
        (automatic_MM_power_restrict (K := K) 0 m 1 1 1 hblock
          (gradeFour_row_word_allowed m))
    · simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
      norm_num [componentBase]
  · refine ⟨1, 1, 1, ?_, ?_⟩
    · have hblock : TensorObj.Restrict (MMObj K 1 1 1)
          (canonicalComponentBlock K (1 : Fin 15)) := by
        simpa [canonicalComponentBlock, shapeX, shapeY, shapeZ] using h1
      simpa only [one_pow] using
        (automatic_MM_power_restrict (K := K) 1 m 1 1 1 hblock
          (row1_word_allowed m))
    · simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
      norm_num [componentBase]
  · refine ⟨1, 1, 1, ?_, ?_⟩
    · have hblock : TensorObj.Restrict (MMObj K 1 1 1)
          (canonicalComponentBlock K (2 : Fin 15)) := by
        simpa [canonicalComponentBlock, shapeX, shapeY, shapeZ] using h2
      simpa only [one_pow] using
        (automatic_MM_power_restrict (K := K) 2 m 1 1 1 hblock
          (row2_word_allowed m))
    · simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
      norm_num [componentBase]
  · let n := MME.DWZTable2Counts.component (6 : Fin 15) * m
    refine ⟨1, 12 ^ n, 1, ?_, ?_⟩
    · have hblock : TensorObj.Restrict (MMObj K 1 12 1)
          (canonicalComponentBlock K (6 : Fin 15)) := by
        simpa [canonicalComponentBlock, shapeX, shapeY, shapeZ] using h6
      simpa only [one_pow, n] using
        (automatic_MM_power_restrict (K := K) 6 m 1 12 1 hblock
          (row6_word_allowed m))
    · simpa only [componentBase, Fin.isValue, ↓reduceIte, zero_mul,
          neg_zero, Real.exp_zero, mul_one, one_mul, n] using
        (le_of_eq (volume_rpow_identity 12 n tau))
  · let n := MME.DWZTable2Counts.component (8 : Fin 15) * m
    refine ⟨1, 12 ^ n, 1, ?_, ?_⟩
    · have hblock : TensorObj.Restrict (MMObj K 1 12 1)
          (canonicalComponentBlock K (8 : Fin 15)) := by
        simpa [canonicalComponentBlock, shapeX, shapeY, shapeZ] using h8
      simpa only [one_pow, n] using
        (automatic_MM_power_restrict (K := K) 8 m 1 12 1 hblock
          (row8_word_allowed m))
    · simpa only [componentBase, Fin.isValue, ↓reduceIte, zero_mul,
          neg_zero, Real.exp_zero, mul_one, one_mul, n] using
        (le_of_eq (volume_rpow_identity 12 n tau))
  · let n := MME.DWZTable2Counts.component (11 : Fin 15) * m
    refine ⟨1, 38 ^ n, 1, ?_, ?_⟩
    · have hblock : TensorObj.Restrict (MMObj K 1 38 1)
          (canonicalComponentBlock K (11 : Fin 15)) := by
        simpa [canonicalComponentBlock, shapeX, shapeY, shapeZ] using h11
      simpa only [one_pow, n] using
        (automatic_MM_power_restrict (K := K) 11 m 1 38 1 hblock
          (row11_word_allowed m))
    · simpa only [componentBase, Fin.isValue, ↓reduceIte, zero_mul,
          neg_zero, Real.exp_zero, mul_one, one_mul, n] using
        (le_of_eq (volume_rpow_identity 38 n tau))
