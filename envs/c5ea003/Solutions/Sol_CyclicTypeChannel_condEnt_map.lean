-- Prove2me | solution 1 for CyclicTypeChannel.condEnt_map
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:22:51.758619+00:00
-- url     : https://prove2.me/submissions/9821788c-3326-40d4-855d-bf0bb11cdbf6

-- Sol generated from Shared/CyclicTypeChannelProduct.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Theorems.Thm_CyclicTypeChannel_uEnt_map
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








/-! ## 2. Transport: relabelling the sample set and recoding the read-out -/


variable [DecidableEq β] [DecidableEq γ]

















open CyclicTypeChannel in
theorem solution{s : Finset α} (e : α ↪ α') (g : α' → β) (k : α' → γ) :
    condEnt (s.map e) g k = condEnt s (g ∘ e) (k ∘ e) := by
  classical
  have himg : (s.map e).image k = s.image (k ∘ e) := by
    ext c
    simp only [mem_image, mem_map, Function.comp_apply]
    constructor
    · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩; exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨e a, ⟨a, ha, rfl⟩, rfl⟩
  rw [condEnt, condEnt, himg, Finset.card_map]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hfil : {x ∈ s.map e | k x = c} = ({x ∈ s | (k ∘ e) x = c}).map e := by
    rw [Finset.filter_map]
    rfl
  rw [hfil, Finset.card_map, uEnt_map]
