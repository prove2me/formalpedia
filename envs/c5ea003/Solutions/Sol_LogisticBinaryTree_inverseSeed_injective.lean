-- Prove2me | solution 1 for LogisticBinaryTree.inverseSeed_injective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T15:19:44.050016+00:00
-- url     : https://prove2.me/submissions/0da67411-9f35-4545-9bd8-68163b84a7b5

import Mathlib
import Definitions.Def_Bridges_LogisticCryptographyDeepening_BinaryPreimageTree
open LogisticBinaryTree Set in
theorem solution (n : ℕ) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    Function.Injective (fun bits : Fin n → Bool => inverseSeed n bits y) := by
  -- for `z ∈ (0,1)`: `√(1 - z) ∈ (0,1)`
  have hsq : ∀ z ∈ Ioo (0 : ℝ) 1, 0 < Real.sqrt (1 - z) ∧ Real.sqrt (1 - z) < 1 := by
    rintro z ⟨hz0, hz1⟩
    refine ⟨Real.sqrt_pos.mpr (by linarith), ?_⟩
    rw [Real.sqrt_lt' one_pos]
    linarith
  -- the lower branch lands in `(0, 1/2)`, the upper in `(1/2, 1)`
  have hlow : ∀ z ∈ Ioo (0 : ℝ) 1, 0 < lower z ∧ lower z < 1 / 2 := by
    intro z hz
    obtain ⟨h1, h2⟩ := hsq z hz
    unfold lower
    constructor <;> linarith
  have hup : ∀ z ∈ Ioo (0 : ℝ) 1, 1 / 2 < upper z ∧ upper z < 1 := by
    intro z hz
    obtain ⟨h1, h2⟩ := hsq z hz
    unfold upper
    constructor <;> linarith
  have hbr : ∀ (b : Bool) (z : ℝ), z ∈ Ioo (0 : ℝ) 1 → branch b z ∈ Ioo (0 : ℝ) 1 := by
    intro b z hz
    cases b
    · simp only [branch, Bool.false_eq_true, if_false]
      exact ⟨(hlow z hz).1, by linarith [(hlow z hz).2]⟩
    · simp only [branch, if_true]
      exact ⟨by linarith [(hup z hz).1], (hup z hz).2⟩
  have hin : ∀ (m : ℕ) (bits : Fin m → Bool), inverseSeed m bits y ∈ Ioo (0 : ℝ) 1 := by
    intro m
    induction m with
    | zero => intro bits; exact hy
    | succ m ih => intro bits; exact hbr _ _ (ih _)
  -- each branch is injective on `(0,1)`
  have hsqrt_inj : ∀ z₁ ∈ Ioo (0 : ℝ) 1, ∀ z₂ ∈ Ioo (0 : ℝ) 1,
      Real.sqrt (1 - z₁) = Real.sqrt (1 - z₂) → z₁ = z₂ := by
    intro z₁ h₁ z₂ h₂ h
    have := (Real.sqrt_inj (by linarith [h₁.2]) (by linarith [h₂.2])).mp h
    linarith
  -- a branch value determines both the bit and the argument
  have hdet : ∀ (b₁ b₂ : Bool) (z₁ z₂ : ℝ), z₁ ∈ Ioo (0 : ℝ) 1 → z₂ ∈ Ioo (0 : ℝ) 1 →
      branch b₁ z₁ = branch b₂ z₂ → b₁ = b₂ ∧ z₁ = z₂ := by
    intro b₁ b₂ z₁ z₂ h₁ h₂ h
    cases b₁ <;> cases b₂ <;> simp only [branch, Bool.false_eq_true, if_false, if_true] at h
    · refine ⟨rfl, hsqrt_inj z₁ h₁ z₂ h₂ ?_⟩
      unfold lower at h
      linarith
    · exact absurd h (by linarith [(hlow z₁ h₁).2, (hup z₂ h₂).1])
    · exact absurd h (by linarith [(hup z₁ h₁).1, (hlow z₂ h₂).2])
    · refine ⟨rfl, hsqrt_inj z₁ h₁ z₂ h₂ ?_⟩
      unfold upper at h
      linarith
  induction n with
  | zero =>
    intro b₁ b₂ _
    funext i
    exact i.elim0
  | succ n ih =>
    intro b₁ b₂ h
    simp only [inverseSeed] at h
    obtain ⟨h0, htail⟩ := hdet _ _ _ _ (hin _ _) (hin _ _) h
    have htl := ih htail
    funext i
    refine Fin.cases h0 (fun j => ?_) i
    exact congrFun htl j
