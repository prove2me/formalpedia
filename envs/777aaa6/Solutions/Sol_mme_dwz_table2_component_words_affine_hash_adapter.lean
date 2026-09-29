-- Prove2me | solution 1 for mme_dwz_table2_component_words_affine_hash_adapter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T04:56:25.126284+00:00
-- url     : https://prove2.me/submissions/64c11b7d-c214-44c6-82c7-c6a3446cd1b6

import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_Fin5_word_difference_nonzero_in_ZMod

set_option autoImplicit false
set_option warningAsError true

open MME

private theorem shape_eq_of_xy_eq {s s' : Fin 15}
    (hX : MME.DWZSquare.shapeX s = MME.DWZSquare.shapeX s')
    (hY : MME.DWZSquare.shapeY s = MME.DWZSquare.shapeY s') :
    s = s' := by
  fin_cases s <;> fin_cases s' <;>
    simp_all [MME.DWZSquare.shapeX, MME.DWZSquare.shapeY]

private theorem other_word_ne
    {N : ℕ} (w w' : Fin (N + 1) → Fin 15) (hww' : w ≠ w') :
    ((fun t ↦ MME.DWZSquare.shapeX (w t)) =
        (fun t ↦ MME.DWZSquare.shapeX (w' t)) →
      (fun t ↦ MME.DWZSquare.shapeY (w t)) ≠
        (fun t ↦ MME.DWZSquare.shapeY (w' t))) ∧
    ((fun t ↦ MME.DWZSquare.shapeY (w t)) =
        (fun t ↦ MME.DWZSquare.shapeY (w' t)) →
      (fun t ↦ MME.DWZSquare.shapeX (w t)) ≠
        (fun t ↦ MME.DWZSquare.shapeX (w' t))) := by
  constructor
  · intro hX hY
    apply hww'
    funext t
    exact shape_eq_of_xy_eq (congrFun hX t) (congrFun hY t)
  · intro hY hX
    apply hww'
    funext t
    exact shape_eq_of_xy_eq (congrFun hX t) (congrFun hY t)

private theorem Fin5_word_cast_ne
    {p N : ℕ} (hp : 5 ≤ p)
    (x y : Fin (N + 1) → Fin 5) (hxy : x ≠ y) :
    (fun t ↦ ((x t).val : ZMod p)) ≠
      (fun t ↦ ((y t).val : ZMod p)) := by
  obtain ⟨j, hj⟩ :=
    mme_Fin5_word_difference_nonzero_in_ZMod hp x y hxy
  intro hcast
  apply hj
  exact sub_eq_zero.mpr (congrFun hcast j)

theorem solution
    {p N : ℕ} (hp : 5 ≤ p)
    (w w' : Fin (N + 1) → Fin 15) (hww' : w ≠ w')
    (hshare :
      (fun t ↦ MME.DWZSquare.shapeX (w t)) =
          (fun t ↦ MME.DWZSquare.shapeX (w' t)) ∨
        (fun t ↦ MME.DWZSquare.shapeY (w t)) =
          (fun t ↦ MME.DWZSquare.shapeY (w' t))) :
    let I : Fin (N + 1) → ZMod p := fun t ↦
      (MME.DWZSquare.shapeX (w t)).val
    let J : Fin (N + 1) → ZMod p := fun t ↦
      (MME.DWZSquare.shapeY (w t)).val
    let K : Fin (N + 1) → ZMod p := fun t ↦
      (MME.DWZSquare.shapeZ (w t)).val
    let I' : Fin (N + 1) → ZMod p := fun t ↦
      (MME.DWZSquare.shapeX (w' t)).val
    let J' : Fin (N + 1) → ZMod p := fun t ↦
      (MME.DWZSquare.shapeY (w' t)).val
    let K' : Fin (N + 1) → ZMod p := fun t ↦
      (MME.DWZSquare.shapeZ (w' t)).val
    (∀ t, I t + J t + K t = (4 : ZMod p)) ∧
      (∀ t, I' t + J' t + K' t = (4 : ZMod p)) ∧
      ((I = I' ∧ J ≠ J') ∨ (J = J' ∧ I ≠ I')) := by
  dsimp only
  have hsupport (u : Fin (N + 1) → Fin 15) (t : Fin (N + 1)) :
      ((MME.DWZSquare.shapeX (u t)).val : ZMod p) +
          ((MME.DWZSquare.shapeY (u t)).val : ZMod p) +
          ((MME.DWZSquare.shapeZ (u t)).val : ZMod p) = 4 := by
    have hsum := MME.DWZSquare.shape_sum (u t)
    have hcast := congrArg (fun n : ℕ ↦ (n : ZMod p)) hsum
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hcast
  refine ⟨hsupport w, hsupport w', ?_⟩
  rcases hshare with hX | hY
  · left
    refine ⟨?_, ?_⟩
    · funext t
      rw [congrFun hX t]
    · exact Fin5_word_cast_ne hp _ _ ((other_word_ne w w' hww').1 hX)
  · right
    refine ⟨?_, ?_⟩
    · funext t
      rw [congrFun hY t]
    · exact Fin5_word_cast_ne hp _ _ ((other_word_ne w w' hww').2 hY)

