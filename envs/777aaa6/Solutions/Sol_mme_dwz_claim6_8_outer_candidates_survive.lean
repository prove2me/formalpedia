-- Prove2me | solution 1 for mme_dwz_claim6_8_outer_candidates_survive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T19:14:39.236385+00:00
-- url     : https://prove2.me/submissions/c8b0477d-910f-4484-9d6a-fd31d9702120

import Theorems.Thm_mme_dwz_claim6_8_concrete_bounded_address_survival

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p n levelSum : ℕ} [Fact p.Prime]
    {Outer : Type*} [Fintype Outer] [DecidableEq Outer]
    (hpodd : Odd p) (hlevel : levelSum < p) (b0 : ZMod p)
    (addressX : Outer → Fin (n + 1) → Fin (levelSum + 1))
    (haddressX : Function.Injective addressX)
    (retained : Outer)
    (K : Fin (n + 1) → Fin (levelSum + 1))
    (compatible : Outer → Prop) [DecidablePred compatible]
    (bad : (Fin (n + 1) → ZMod p) → Prop) [DecidablePred bad] :
    let outerCandidates :=
      Finset.univ.filter (fun A : Outer ↦ A ≠ retained ∧ compatible A)
    let hX : (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → Fin (levelSum + 1)) → ZMod p :=
      fun w A ↦ b0 + ∑ t, ((A t).val : ZMod p) * w t
    let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → Fin (levelSum + 1)) → ZMod p :=
      fun w0 w C ↦
        b0 + (2 : ZMod p)⁻¹ *
          (w0 + ∑ t, ((levelSum : ZMod p) - (C t).val) * w t)
    let conditionedW0 : (Fin (n + 1) → ZMod p) → ZMod p :=
      fun w ↦
        2 * (∑ t, ((addressX retained t).val : ZMod p) * w t) -
          ∑ t, ((levelSum : ZMod p) - (K t).val) * w t
    (∀ w, bad w →
      ∃ A ∈ outerCandidates,
        hX w (addressX A) = hZ (conditionedW0 w) w K) →
    8 * outerCandidates.card ≤ p →
    8 * (Finset.univ.filter bad).card ≤
      Fintype.card (Fin (n + 1) → ZMod p) := by
  classical
  dsimp only
  intro hbad hbudget
  let outerCandidates : Finset Outer :=
    Finset.univ.filter (fun A : Outer ↦ A ≠ retained ∧ compatible A)
  let addressCandidates :
      Finset (Fin (n + 1) → Fin (levelSum + 1)) :=
    outerCandidates.image addressX
  have hcard : addressCandidates.card = outerCandidates.card := by
    exact Finset.card_image_of_injective outerCandidates haddressX
  have hdistinct : ∀ A ∈ addressCandidates, A ≠ addressX retained := by
    intro A hA hEq
    obtain ⟨source, hsource, rfl⟩ := Finset.mem_image.mp hA
    have hsourceNe : source ≠ retained :=
      (Finset.mem_filter.mp hsource).2.1
    exact hsourceNe (haddressX hEq)
  apply mme_dwz_claim6_8_concrete_bounded_address_survival
    hpodd hlevel b0 (addressX retained) K addressCandidates hdistinct bad
  · intro w hw
    obtain ⟨source, hsource, hcollision⟩ := hbad w hw
    exact ⟨addressX source,
      Finset.mem_image.mpr ⟨source, hsource, rfl⟩, hcollision⟩
  · simpa only [hcard] using hbudget
