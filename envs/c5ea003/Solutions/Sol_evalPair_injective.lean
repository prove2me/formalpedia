-- Prove2me | solution 1 for evalPair_injective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T06:05:21.372328+00:00
-- url     : https://prove2.me/submissions/8d2f794a-d483-4be3-8e8b-bdd76e1b1ef0

import Mathlib
import Definitions.Def_Cryptography_PosetTheory_BerggrenGreenIncomparability
theorem solution : Function.Injective evalPair := by
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
  exact fun w₁ w₂ h => hinjP w₁ w₂ h
