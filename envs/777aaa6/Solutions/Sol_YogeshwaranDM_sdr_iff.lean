-- Prove2me | solution 1 for YogeshwaranDM.sdr_iff
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:52:58.46446+00:00
-- url     : https://prove2.me/submissions/2a249a8a-aece-4423-9a07-4e74e7f20be8

import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Set.Card
import Mathlib.Tactic

set_option autoImplicit false

theorem solution {ι α : Type*} [Fintype ι] (A : ι → Set α) :
    (∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∈ A i) ↔
      ∀ I : Finset ι, (I.card : ℕ∞) ≤ (⋃ i ∈ I, A i).encard := by
  classical
  constructor
  · rintro ⟨f, hf, hfA⟩ I
    calc
      (I.card : ℕ∞) = ((I.image f : Finset α) : Set α).encard := by
        rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective I hf]
      _ ≤ (⋃ i ∈ I, A i).encard := Set.encard_mono (by
        intro a ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hfA i⟩⟩)
  · intro h
    have witness (I : Finset ι) :
        ∃ t : Finset α, (↑t : Set α) ⊆ (⋃ i ∈ I, A i) ∧ I.card = t.card := by
      obtain ⟨t, ht, hc⟩ := Set.exists_subset_encard_eq (h I)
      have htf : t.Finite := Set.finite_of_encard_eq_coe hc
      refine ⟨htf.toFinset, by simpa using ht, ?_⟩
      have he := htf.encard_eq_coe_toFinset_card
      rw [hc] at he
      exact ENat.coe_inj.mp he
    choose t ht hc using witness
    let B : Finset α := Finset.univ.biUnion t
    let A' (i : ι) : Finset α := B.filter (fun a => a ∈ A i)
    have hfinite (I : Finset ι) : I.card ≤ (I.biUnion A').card := by
      rw [hc I]
      apply Finset.card_le_card
      intro a ha
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht I ha)
      obtain ⟨hiI, hai⟩ := Set.mem_iUnion.mp hi
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hiI, Finset.mem_filter.mpr ⟨?_, hai⟩⟩
      exact Finset.mem_biUnion.mpr ⟨I, Finset.mem_univ I, ha⟩
    obtain ⟨f, hf, hfA⟩ :=
      (Finset.all_card_le_biUnion_card_iff_existsInjective' A').mp hfinite
    exact ⟨f, hf, fun i => (Finset.mem_filter.mp (hfA i)).2⟩
