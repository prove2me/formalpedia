-- Prove2me | solution 1 for CyclicTypeChannel.uEnt_prod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:16:27.913883+00:00
-- url     : https://prove2.me/submissions/9bbee5eb-37b0-41e8-b943-2160361c0d53

-- Sol generated from Shared/CyclicTypeChannelProduct.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Theorems.Thm_CyclicTypeChannel_fiber_card_pos
/-
# Additivity of the counting channel over independent products

The exact values of the cyclic type-pair channel obey an unexpected law:
for coprime cyclic orders the information is *additive*,
`I_pair (m * n) = I_pair m + I_pair n`.

This file proves the structural reason.  In the counting-entropy framework of
`Shared.CyclicTypeChannel` we show that entropy, conditional entropy and mutual
information are **exactly additive over cartesian products** of the underlying
sample sets when both the read-out and the conditioning variable act
coordinatewise.  Together with the transport lemmas (invariance of the channel
under a relabelling of the sample set and under an injective recoding of the
read-out) this turns the Chinese Remainder Theorem into an additivity law for
the splitting-type channel.
-/

open CyclicTypeChannel

open Finset

variable {α α' β β' γ γ' : Type*}

/-! ## 1. Fibres of a coordinatewise read-out -/


variable {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type*}

/-- The fibre of a coordinatewise read-out over a product set is the product of
the two fibres. -/
lemma filter_prod_eq [DecidableEq β₁] [DecidableEq β₂]
    (s₁ : Finset α₁) (s₂ : Finset α₂) (g₁ : α₁ → β₁) (g₂ : α₂ → β₂) (v₁ : β₁) (v₂ : β₂) :
    {x ∈ s₁ ×ˢ s₂ | (g₁ x.1, g₂ x.2) = (v₁, v₂)}
      = {x ∈ s₁ | g₁ x = v₁} ×ˢ {x ∈ s₂ | g₂ x = v₂} := by
  ext ⟨u, v⟩
  simp only [mem_filter, mem_product, Prod.mk.injEq]
  tauto

lemma card_filter_prod [DecidableEq β₁] [DecidableEq β₂]
    (s₁ : Finset α₁) (s₂ : Finset α₂) (g₁ : α₁ → β₁) (g₂ : α₂ → β₂) (v₁ : β₁) (v₂ : β₂) :
    (#{x ∈ s₁ ×ˢ s₂ | (g₁ x.1, g₂ x.2) = (v₁, v₂)})
      = (#{x ∈ s₁ | g₁ x = v₁}) * (#{x ∈ s₂ | g₂ x = v₂}) := by
  rw [filter_prod_eq, card_product]






/-! ## 2. Transport: relabelling the sample set and recoding the read-out -/


variable [DecidableEq β] [DecidableEq γ]

















open CyclicTypeChannel in
theorem solution[DecidableEq β₁] [DecidableEq β₂] {s₁ : Finset α₁} {s₂ : Finset α₂}
    (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty) (g₁ : α₁ → β₁) (g₂ : α₂ → β₂) :
    uEnt (s₁ ×ˢ s₂) (fun x => (g₁ x.1, g₂ x.2)) = uEnt s₁ g₁ + uEnt s₂ g₂ := by
  classical
  have hc₁ : (0 : ℝ) < s₁.card := by exact_mod_cast card_pos.2 h₁
  have hc₂ : (0 : ℝ) < s₂.card := by exact_mod_cast card_pos.2 h₂
  have hsum : ∑ x ∈ s₁ ×ˢ s₂,
        Real.logb 2 (#{y ∈ s₁ ×ˢ s₂ | (g₁ y.1, g₂ y.2) = (g₁ x.1, g₂ x.2)} : ℝ)
      = (s₂.card : ℝ) * (∑ a ∈ s₁, Real.logb 2 (#{x ∈ s₁ | g₁ x = g₁ a} : ℝ))
        + (s₁.card : ℝ) * (∑ b ∈ s₂, Real.logb 2 (#{x ∈ s₂ | g₂ x = g₂ b} : ℝ)) := by
    rw [Finset.sum_product]
    have hterm : ∀ a ∈ s₁, ∑ b ∈ s₂,
        Real.logb 2 (#{y ∈ s₁ ×ˢ s₂ | (g₁ y.1, g₂ y.2) = (g₁ a, g₂ b)} : ℝ)
        = (s₂.card : ℝ) * Real.logb 2 (#{x ∈ s₁ | g₁ x = g₁ a} : ℝ)
          + ∑ b ∈ s₂, Real.logb 2 (#{x ∈ s₂ | g₂ x = g₂ b} : ℝ) := by
      intro a ha
      have : ∀ b ∈ s₂,
          Real.logb 2 (#{y ∈ s₁ ×ˢ s₂ | (g₁ y.1, g₂ y.2) = (g₁ a, g₂ b)} : ℝ)
          = Real.logb 2 (#{x ∈ s₁ | g₁ x = g₁ a} : ℝ)
            + Real.logb 2 (#{x ∈ s₂ | g₂ x = g₂ b} : ℝ) := by
        intro b hb
        have hp₁ : (0 : ℝ) < (#{x ∈ s₁ | g₁ x = g₁ a} : ℝ) := by
          exact_mod_cast fiber_card_pos ha
        have hp₂ : (0 : ℝ) < (#{x ∈ s₂ | g₂ x = g₂ b} : ℝ) := by
          exact_mod_cast fiber_card_pos hb
        rw [show ((#{y ∈ s₁ ×ˢ s₂ | (g₁ y.1, g₂ y.2) = (g₁ a, g₂ b)} : ℕ) : ℝ)
            = ((#{x ∈ s₁ | g₁ x = g₁ a} : ℕ) : ℝ) * ((#{x ∈ s₂ | g₂ x = g₂ b} : ℕ) : ℝ) from by
          exact_mod_cast congrArg (Nat.cast (R := ℝ)) (card_filter_prod s₁ s₂ g₁ g₂ _ _),
          Real.logb_mul (ne_of_gt hp₁) (ne_of_gt hp₂)]
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul]
  rw [uEnt, uEnt, uEnt, hsum, card_product]
  push_cast
  rw [Real.logb_mul (ne_of_gt hc₁) (ne_of_gt hc₂)]
  field_simp
  ring
