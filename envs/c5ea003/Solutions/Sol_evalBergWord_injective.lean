-- Prove2me | solution 1 for evalBergWord_injective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:59:44.652015+00:00
-- url     : https://prove2.me/submissions/8f9548f7-46cb-415d-acf6-1ae8ab106e64

import Mathlib
import Definitions.Def_Cryptography_PosetTheory_BerggrenGreenIncomparability
theorem solution : Function.Injective evalBergWord := by
  have hact : ∀ (g : BergGen) (p q : ℤ × ℤ), actGen g p = actGen g q → p = q := by
    intro g p q h
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    cases g <;>
      (simp only [actGen, Prod.mk.injEq] at h
       obtain ⟨h1, h2⟩ := h
       simp only [Prod.mk.injEq]
       omega)
  have hvalid : ∀ w : BergWord, 0 < (evalPair w).2 ∧ (evalPair w).2 < (evalPair w).1 := by
    intro w
    induction w with
    | nil => simp [evalPair, rootPair]
    | cons g w ih =>
      obtain ⟨h1, h2⟩ := ih
      cases g <;> (simp only [evalPair, actGen] at * <;> omega)
  have hclassA : ∀ w : BergWord, (evalPair (BergGen.A :: w)).1 < 2 * (evalPair (BergGen.A :: w)).2 := by
    intro w
    obtain ⟨h1, h2⟩ := hvalid w
    simp only [evalPair, actGen]
    omega
  have hclassB : ∀ w : BergWord, 2 * (evalPair (BergGen.B :: w)).2 < (evalPair (BergGen.B :: w)).1
      ∧ (evalPair (BergGen.B :: w)).1 < 3 * (evalPair (BergGen.B :: w)).2 := by
    intro w
    obtain ⟨h1, h2⟩ := hvalid w
    simp only [evalPair, actGen]
    omega
  have hclassC : ∀ w : BergWord, 3 * (evalPair (BergGen.C :: w)).2 < (evalPair (BergGen.C :: w)).1 := by
    intro w
    obtain ⟨h1, h2⟩ := hvalid w
    simp only [evalPair, actGen]
    omega
  have hroot : (evalPair ([] : BergWord)).1 = 2 * (evalPair ([] : BergWord)).2 := by
    simp [evalPair, rootPair]
  have hgen : ∀ (g₁ g₂ : BergGen) (w₁ w₂ : BergWord),
      evalPair (g₁ :: w₁) = evalPair (g₂ :: w₂) → g₁ = g₂ := by
    intro g₁ g₂ w₁ w₂ h
    have hv₁ := hvalid (g₁ :: w₁)
    have hv₂ := hvalid (g₂ :: w₂)
    cases g₁ <;> cases g₂ <;>
      first
        | rfl
        | (exfalso
           have ha₁ := hclassA w₁
           have ha₂ := hclassA w₂
           have hb₁ := hclassB w₁
           have hb₂ := hclassB w₂
           have hc₁ := hclassC w₁
           have hc₂ := hclassC w₂
           rw [h] at *
           omega)
  have hinjP : ∀ w₁ w₂ : BergWord, evalPair w₁ = evalPair w₂ → w₁ = w₂ := by
    intro w₁
    induction w₁ with
    | nil =>
      intro w₂ h
      cases w₂ with
      | nil => rfl
      | cons g₂ w₂ =>
        exfalso
        have hv := hvalid (g₂ :: w₂)
        have h1 : (evalPair (g₂ :: w₂)).1 = 2 := by
          rw [← h]
          simp [evalPair, rootPair]
        have h2 : (evalPair (g₂ :: w₂)).2 = 1 := by
          rw [← h]
          simp [evalPair, rootPair]
        cases g₂
        · have ha := hclassA w₂
          omega
        · have hb := hclassB w₂
          omega
        · have hc := hclassC w₂
          omega
    | cons g₁ w₁ ih =>
      intro w₂ h
      cases w₂ with
      | nil =>
        exfalso
        have hv := hvalid (g₁ :: w₁)
        have h1 : (evalPair (g₁ :: w₁)).1 = 2 := by
          rw [h]
          simp [evalPair, rootPair]
        have h2 : (evalPair (g₁ :: w₁)).2 = 1 := by
          rw [h]
          simp [evalPair, rootPair]
        cases g₁
        · have ha := hclassA w₁
          omega
        · have hb := hclassB w₁
          omega
        · have hc := hclassC w₁
          omega
      | cons g₂ w₂ =>
        have hg : g₁ = g₂ := hgen g₁ g₂ w₁ w₂ h
        subst hg
        simp only [evalPair] at h
        have := hact g₁ _ _ h
        rw [ih w₂ this]
  have hentry : ∀ (g : BergGen) (M : Matrix (Fin 2) (Fin 2) ℤ) (i j : Fin 2),
      (bergMat g * M) i j = bergMat g i 0 * M 0 j + bergMat g i 1 * M 1 j := by
    intro g M i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  have hstep : ∀ (g : BergGen) (M : Matrix (Fin 2) (Fin 2) ℤ),
      pairOfMat (bergMat g * M) = actGen g (pairOfMat M) := by
    intro g M
    simp only [pairOfMat, hentry]
    cases g <;>
      (simp only [bergMat, actGen, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
          Prod.mk.injEq]
       constructor <;> ring)
  have hbridge : ∀ w : BergWord, pairOfMat (evalBergWord w) = evalPair w := by
    intro w
    induction w with
    | nil =>
      show pairOfMat (1 : Matrix (Fin 2) (Fin 2) ℤ) = rootPair
      simp only [pairOfMat, rootPair, Matrix.one_apply_eq, Matrix.one_apply_ne, Prod.mk.injEq]
      norm_num
    | cons g w ih =>
      show pairOfMat (bergMat g * evalBergWord w) = actGen g (evalPair w)
      rw [hstep g (evalBergWord w), ih]
  intro w₁ w₂ h
  exact hinjP w₁ w₂ (by rw [← hbridge w₁, ← hbridge w₂, h])
