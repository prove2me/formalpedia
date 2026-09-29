-- Prove2me | solution 1 for mme_more_asymmetry_boundary_word_to_complementary_splits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T18:53:06.974235+00:00
-- url     : https://prove2.me/submissions/274eaf19-7c31-4950-bc89-9b07f2f6d3cd

import Definitions.Def_mme_recursive_yz_physical_words

open MME.CompleteSplit MME.RecursiveThinSplit MME.RecursiveYZ
set_option autoImplicit false

theorem solution (p : Fin 3 → ℕ)
    (hp0 : p 0 = 0)
    (htotal : p 0 + p 1 + p 2 = 2 * 4)
    (w : CompleteWord 3)
    (hw : (w 0).val + (w 1).val + (w 2).val + (w 3).val = p 1) :
    ∃ sL : Split 4 p,
      (sL.val 0).val = 0 ∧
      (sL.val 1).val = (w 0).val + (w 1).val ∧
      (sL.val 2).val = 4 - ((w 0).val + (w 1).val) ∧
      ((complement htotal sL).val 0).val = 0 ∧
      ((complement htotal sL).val 1).val = (w 2).val + (w 3).val ∧
      ((complement htotal sL).val 2).val = 4 - ((w 2).val + (w 3).val) := by
  classical
  let a := (w 0).val + (w 1).val
  let b := (w 2).val + (w 3).val
  have hw0Lt : (w 0).val < 3 := (w 0).isLt
  have hw1Lt : (w 1).val < 3 := (w 1).isLt
  have hw2Lt : (w 2).val < 3 := (w 2).isLt
  have hw3Lt : (w 3).val < 3 := (w 3).isLt
  have hw0 : (w 0).val ≤ 2 := by omega
  have hw1 : (w 1).val ≤ 2 := by omega
  have hw2 : (w 2).val ≤ 2 := by omega
  have hw3 : (w 3).val ≤ 2 := by omega
  have hab : a + b = p 1 := by dsimp [a, b]; omega
  have ha : a ≤ 4 := by dsimp [a]; omega
  have hb : b ≤ 4 := by dsimp [b]; omega
  let x : Fin 3 → Fin 5 := fun i =>
    ⟨if i = 0 then 0 else if i = 1 then a else 4 - a, by
      fin_cases i
      · simp
      · simp; omega
      · simp; omega⟩
  have hx0 : (x 0).val = 0 := by simp [x]
  have hx1 : (x 1).val = a := by simp [x]
  have hx2 : (x 2).val = 4 - a := by simp [x]
  have hxsum : (x 0).val + (x 1).val + (x 2).val = 4 := by
    rw [hx0, hx1, hx2]
    omega
  have hxle : ∀ i, (x i).val ≤ p i := by
    intro i
    fin_cases i
    · simp [x, hp0]
    · simp [x]
      omega
    · simp [x]
      omega
  let sL : Split 4 p := ⟨x, ⟨hxsum, hxle⟩⟩
  refine ⟨sL, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (x 0).val = 0
    exact hx0
  · change (x 1).val = (w 0).val + (w 1).val
    exact hx1
  · change (x 2).val = 4 - ((w 0).val + (w 1).val)
    exact hx2
  · change p 0 - (x 0).val = 0
    simp [hp0, hx0]
  · change p 1 - (x 1).val = (w 2).val + (w 3).val
    omega
  · change p 2 - (x 2).val = 4 - ((w 2).val + (w 3).val)
    omega
