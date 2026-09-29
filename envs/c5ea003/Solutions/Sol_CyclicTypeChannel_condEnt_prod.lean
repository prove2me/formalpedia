-- Prove2me | solution 1 for CyclicTypeChannel.condEnt_prod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:17:45.946649+00:00
-- url     : https://prove2.me/submissions/72e3152a-8204-4c1e-a115-36b110895f84

-- Sol generated from Shared/CyclicTypeChannelProduct.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Theorems.Thm_CyclicTypeChannel_sum_fiber_card
import Theorems.Thm_CyclicTypeChannel_uEnt_prod
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



/-- The image of a coordinatewise read-out over a product is the product of the
images. -/
lemma image_prod_eq [DecidableEq β₁] [DecidableEq β₂]
    (s₁ : Finset α₁) (s₂ : Finset α₂) (g₁ : α₁ → β₁) (g₂ : α₂ → β₂) :
    (s₁ ×ˢ s₂).image (fun x => (g₁ x.1, g₂ x.2)) = (s₁.image g₁) ×ˢ (s₂.image g₂) := by
  ext ⟨v₁, v₂⟩
  simp only [mem_image, mem_product, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, h1, h2⟩
    exact ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩
  · rintro ⟨⟨a, ha, h1⟩, b, hb, h2⟩
    exact ⟨a, b, ⟨ha, hb⟩, h1, h2⟩




/-! ## 2. Transport: relabelling the sample set and recoding the read-out -/


variable [DecidableEq β] [DecidableEq γ]

















open CyclicTypeChannel in
theorem solution[DecidableEq β₁] [DecidableEq β₂] [DecidableEq γ₁] [DecidableEq γ₂]
    {s₁ : Finset α₁} {s₂ : Finset α₂} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty)
    (g₁ : α₁ → β₁) (g₂ : α₂ → β₂) (k₁ : α₁ → γ₁) (k₂ : α₂ → γ₂) :
    condEnt (s₁ ×ˢ s₂) (fun x => (g₁ x.1, g₂ x.2)) (fun x => (k₁ x.1, k₂ x.2))
      = condEnt s₁ g₁ k₁ + condEnt s₂ g₂ k₂ := by
  classical
  have hc₁ : (0 : ℝ) < s₁.card := by exact_mod_cast card_pos.2 h₁
  have hc₂ : (0 : ℝ) < s₂.card := by exact_mod_cast card_pos.2 h₂
  have hmass₁ : ∑ c ∈ s₁.image k₁, ((#{x ∈ s₁ | k₁ x = c} : ℝ) / s₁.card) = 1 := by
    rw [← Finset.sum_div]
    rw [show ∑ c ∈ s₁.image k₁, ((#{x ∈ s₁ | k₁ x = c} : ℕ) : ℝ) = (s₁.card : ℝ) from by
      exact_mod_cast congrArg (Nat.cast (R := ℝ)) (sum_fiber_card s₁ k₁)]
    exact div_self (ne_of_gt hc₁)
  have hmass₂ : ∑ c ∈ s₂.image k₂, ((#{x ∈ s₂ | k₂ x = c} : ℝ) / s₂.card) = 1 := by
    rw [← Finset.sum_div]
    rw [show ∑ c ∈ s₂.image k₂, ((#{x ∈ s₂ | k₂ x = c} : ℕ) : ℝ) = (s₂.card : ℝ) from by
      exact_mod_cast congrArg (Nat.cast (R := ℝ)) (sum_fiber_card s₂ k₂)]
    exact div_self (ne_of_gt hc₂)
  rw [condEnt, image_prod_eq, Finset.sum_product]
  have hterm : ∀ c₁ ∈ s₁.image k₁, ∑ c₂ ∈ s₂.image k₂,
      ((#{x ∈ s₁ ×ˢ s₂ | (k₁ x.1, k₂ x.2) = (c₁, c₂)} : ℝ) / ((s₁ ×ˢ s₂).card)) *
        uEnt {x ∈ s₁ ×ˢ s₂ | (k₁ x.1, k₂ x.2) = (c₁, c₂)} (fun x => (g₁ x.1, g₂ x.2))
      = ((#{x ∈ s₁ | k₁ x = c₁} : ℝ) / s₁.card) * uEnt {x ∈ s₁ | k₁ x = c₁} g₁
        + ((#{x ∈ s₁ | k₁ x = c₁} : ℝ) / s₁.card) * condEnt s₂ g₂ k₂ := by
    intro c₁ hc
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hc
    have hne₁ : ({x ∈ s₁ | k₁ x = k₁ a}).Nonempty := ⟨a, by simp [ha]⟩
    have hstep : ∀ c₂ ∈ s₂.image k₂,
        ((#{x ∈ s₁ ×ˢ s₂ | (k₁ x.1, k₂ x.2) = (k₁ a, c₂)} : ℝ) / ((s₁ ×ˢ s₂).card)) *
          uEnt {x ∈ s₁ ×ˢ s₂ | (k₁ x.1, k₂ x.2) = (k₁ a, c₂)} (fun x => (g₁ x.1, g₂ x.2))
        = ((#{x ∈ s₁ | k₁ x = k₁ a} : ℝ) / s₁.card) *
            (((#{x ∈ s₂ | k₂ x = c₂} : ℝ) / s₂.card) *
              (uEnt {x ∈ s₁ | k₁ x = k₁ a} g₁ + uEnt {x ∈ s₂ | k₂ x = c₂} g₂)) := by
      intro c₂ hc₂'
      obtain ⟨b, hb, rfl⟩ := mem_image.1 hc₂'
      have hne₂ : ({x ∈ s₂ | k₂ x = k₂ b}).Nonempty := ⟨b, by simp [hb]⟩
      rw [filter_prod_eq, uEnt_prod hne₁ hne₂, card_product, card_product]
      push_cast
      field_simp
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
    have : ∑ c₂ ∈ s₂.image k₂, ((#{x ∈ s₂ | k₂ x = c₂} : ℝ) / s₂.card) *
        (uEnt {x ∈ s₁ | k₁ x = k₁ a} g₁ + uEnt {x ∈ s₂ | k₂ x = c₂} g₂)
        = uEnt {x ∈ s₁ | k₁ x = k₁ a} g₁ + condEnt s₂ g₂ k₂ := by
      rw [condEnt]
      have hexp : ∀ c₂ ∈ s₂.image k₂, ((#{x ∈ s₂ | k₂ x = c₂} : ℝ) / s₂.card) *
          (uEnt {x ∈ s₁ | k₁ x = k₁ a} g₁ + uEnt {x ∈ s₂ | k₂ x = c₂} g₂)
          = ((#{x ∈ s₂ | k₂ x = c₂} : ℝ) / s₂.card) * uEnt {x ∈ s₁ | k₁ x = k₁ a} g₁
            + ((#{x ∈ s₂ | k₂ x = c₂} : ℝ) / s₂.card) * uEnt {x ∈ s₂ | k₂ x = c₂} g₂ := by
        intro c₂ _; ring
      rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, ← Finset.sum_mul, hmass₂, one_mul]
    rw [this]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul, hmass₁, one_mul]
  simp only [condEnt]
