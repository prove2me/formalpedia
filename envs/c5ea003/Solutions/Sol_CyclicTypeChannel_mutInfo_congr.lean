-- Prove2me | solution 1 for CyclicTypeChannel.mutInfo_congr
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:12:05.587813+00:00
-- url     : https://prove2.me/submissions/59385f86-9dc2-4c3e-af2f-588bc524f55e

-- Sol generated from Shared/CyclicTypeChannelProduct.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Theorems.Thm_CyclicTypeChannel_uEnt_congr
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


/-- Conditional entropy only depends on the values of the read-out on the
sample set. -/
theorem condEnt_congr {s : Finset α} {g g' : α → β} {k : α → γ} (h : ∀ a ∈ s, g a = g' a) :
    condEnt s g k = condEnt s g' k :=
  Finset.sum_congr rfl fun c _ => by
    rw [uEnt_congr (fun a ha => h a (mem_of_mem_filter a ha))]

/-- Conditional entropy only depends on the values of the conditioning variable
on the sample set. -/
theorem condEnt_congr_cond {s : Finset α} {g : α → β} {k k' : α → γ} (h : ∀ a ∈ s, k a = k' a) :
    condEnt s g k = condEnt s g k' := by
  have himg : s.image k = s.image k' := Finset.image_congr h
  rw [condEnt, condEnt, himg]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : {x ∈ s | k x = c} = {x ∈ s | k' x = c} := by
    apply Finset.filter_congr
    intro x hx
    rw [h x hx]
  rw [this]














open CyclicTypeChannel in
theorem solution{s : Finset α} {g g' : α → β} {k k' : α → γ} (h : ∀ a ∈ s, g a = g' a)
    (h' : ∀ a ∈ s, k a = k' a) : mutInfo s g k = mutInfo s g' k' := by
  rw [mutInfo, mutInfo, uEnt_congr h, condEnt_congr h, condEnt_congr_cond h']
