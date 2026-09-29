-- Prove2me | solution 1 for MarkoffTransfer.mEval_injective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T06:21:00.433775+00:00
-- url     : https://prove2.me/submissions/5d443594-9ef8-40fa-a7b5-2ab75236b042

import Mathlib
import Definitions.Def_Cryptography_MarkoffTransfer_MarkoffCore
import Definitions.Def_Cryptography_MarkoffTransfer_MarkoffFreeBinary
open MarkoffTransfer in
theorem solution : Function.Injective mEval := by
  have hroot : StrictM mRoot := by
    unfold StrictM mRoot IsMarkoff markoffForm
    norm_num
  have hchildL : ∀ t : ℤ × ℤ × ℤ, StrictM t → StrictM (childL t) := by
    rintro ⟨a, b, c⟩ h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    simp only at h1 h2 h3 h4
    unfold IsMarkoff markoffForm at h5
    simp only at h5
    unfold StrictM childL
    simp only
    refine ⟨by omega, by omega, by nlinarith, by nlinarith, ?_⟩
    unfold IsMarkoff markoffForm
    linear_combination h5
  have hchildR : ∀ t : ℤ × ℤ × ℤ, StrictM t → StrictM (childR t) := by
    rintro ⟨a, b, c⟩ h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    simp only at h1 h2 h3 h4
    unfold IsMarkoff markoffForm at h5
    simp only at h5
    unfold StrictM childR
    simp only
    refine ⟨by omega, by omega, by nlinarith, by nlinarith, ?_⟩
    unfold IsMarkoff markoffForm
    linear_combination h5
  have hstrict : ∀ w : List Bool, StrictM (mEval w) := by
    intro w
    induction w with
    | nil => exact hroot
    | cons b w ih =>
      cases b with
      | false => exact hchildL _ ih
      | true => exact hchildR _ ih
  have hparL : ∀ t : ℤ × ℤ × ℤ, StrictM t → mParent (childL t) = t := by
    rintro ⟨a, b, c⟩ h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    simp only at h1 h2 h3 h4
    unfold mParent childL
    simp only
    rw [show 3 * a * c - (3 * a * c - b) = b from by ring, if_neg (by omega : ¬ b ≤ a)]
  have hparR : ∀ t : ℤ × ℤ × ℤ, StrictM t → mParent (childR t) = t := by
    rintro ⟨a, b, c⟩ h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    simp only at h1 h2 h3 h4
    unfold mParent childR
    simp only
    rw [show 3 * b * c - (3 * b * c - a) = a from by ring, if_pos (by omega : a ≤ b)]
  have hne : ∀ t : ℤ × ℤ × ℤ, StrictM t → childL t ≠ childR t := by
    rintro ⟨a, b, c⟩ h hEq
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    simp only at h1 h2 h3 h4
    unfold childL childR at hEq
    simp only [Prod.mk.injEq] at hEq
    omega
  have hinj : ∀ w₁ w₂ : List Bool, mEval w₁ = mEval w₂ → w₁ = w₂ := by
    intro w₁
    induction w₁ with
    | nil =>
      intro w₂ h
      cases w₂ with
      | nil => rfl
      | cons b₂ w₂ =>
        exfalso
        have hs := hstrict w₂
        obtain ⟨h1, h2, h3, h4, h5⟩ := hs
        cases b₂ with
        | false =>
          have he : mEval (false :: w₂) = childL (mEval w₂) := rfl
          have h0 : mEval ([] : List Bool) = mRoot := rfl
          rw [he, h0] at h
          unfold childL mRoot at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨e1, e2, e3⟩ := h
          nlinarith [h1, h2, h3, h4]
        | true =>
          have he : mEval (true :: w₂) = childR (mEval w₂) := rfl
          have h0 : mEval ([] : List Bool) = mRoot := rfl
          rw [he, h0] at h
          unfold childR mRoot at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨e1, e2, e3⟩ := h
          nlinarith [h1, h2, h3, h4]
    | cons b₁ w₁ ih =>
      intro w₂ h
      cases w₂ with
      | nil =>
        exfalso
        have hs := hstrict w₁
        obtain ⟨h1, h2, h3, h4, h5⟩ := hs
        cases b₁ with
        | false =>
          have he : mEval (false :: w₁) = childL (mEval w₁) := rfl
          have h0 : mEval ([] : List Bool) = mRoot := rfl
          rw [he, h0] at h
          unfold childL mRoot at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨e1, e2, e3⟩ := h
          nlinarith [h1, h2, h3, h4]
        | true =>
          have he : mEval (true :: w₁) = childR (mEval w₁) := rfl
          have h0 : mEval ([] : List Bool) = mRoot := rfl
          rw [he, h0] at h
          unfold childR mRoot at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨e1, e2, e3⟩ := h
          nlinarith [h1, h2, h3, h4]
      | cons b₂ w₂ =>
        have hs₁ := hstrict w₁
        have hs₂ := hstrict w₂
        have hpar : mEval w₁ = mEval w₂ := by
          cases b₁ with
          | false =>
            cases b₂ with
            | false =>
              have e₁ : mEval (false :: w₁) = childL (mEval w₁) := rfl
              have e₂ : mEval (false :: w₂) = childL (mEval w₂) := rfl
              rw [e₁, e₂] at h
              rw [← hparL _ hs₁, ← hparL _ hs₂, h]
            | true =>
              have e₁ : mEval (false :: w₁) = childL (mEval w₁) := rfl
              have e₂ : mEval (true :: w₂) = childR (mEval w₂) := rfl
              rw [e₁, e₂] at h
              rw [← hparL _ hs₁, ← hparR _ hs₂, h]
          | true =>
            cases b₂ with
            | false =>
              have e₁ : mEval (true :: w₁) = childR (mEval w₁) := rfl
              have e₂ : mEval (false :: w₂) = childL (mEval w₂) := rfl
              rw [e₁, e₂] at h
              rw [← hparR _ hs₁, ← hparL _ hs₂, h]
            | true =>
              have e₁ : mEval (true :: w₁) = childR (mEval w₁) := rfl
              have e₂ : mEval (true :: w₂) = childR (mEval w₂) := rfl
              rw [e₁, e₂] at h
              rw [← hparR _ hs₁, ← hparR _ hs₂, h]
        have hb : b₁ = b₂ := by
          cases b₁ <;> cases b₂
          · rfl
          · exfalso
            have e₁ : mEval (false :: w₁) = childL (mEval w₁) := rfl
            have e₂ : mEval (true :: w₂) = childR (mEval w₂) := rfl
            rw [e₁, e₂, hpar] at h
            exact hne _ hs₂ h
          · exfalso
            have e₁ : mEval (true :: w₁) = childR (mEval w₁) := rfl
            have e₂ : mEval (false :: w₂) = childL (mEval w₂) := rfl
            rw [e₁, e₂, hpar] at h
            exact hne _ hs₂ h.symm
          · rfl
        rw [hb, ih w₂ hpar]
  exact fun w₁ w₂ h => hinj w₁ w₂ h
