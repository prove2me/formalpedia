-- Prove2me | solution 1 for UnitalMagmaDefect.defect_le_of_comm_unital
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T01:51:35.030514+00:00
-- url     : https://prove2.me/submissions/e62087ce-7425-4656-99c1-b4a71a08fc2c

import Mathlib
import Definitions.Def_Combinatorics_UnitalMagmaDefect

set_option autoImplicit false
universe u

set_option maxHeartbeats 800000 in
open Finset UnitalMagmaDefect in
theorem solution {M₀ : Type u} [Mul M₀] [Fintype M₀] [DecidableEq M₀]
    (hcomm₀ : ∀ a b : M₀, a * b = b * a)
    {M₁ : Type u} [Mul M₁] [One M₁] [Fintype M₁] [DecidableEq M₁]
    (hl₁ : ∀ a : M₁, (1 : M₁) * a = a) (hr₁ : ∀ a : M₁, a * (1 : M₁) = a)
    {M : Type u} [Mul M] [One M] [Fintype M] [DecidableEq M]
    (hcomm : ∀ a b : M, a * b = b * a)
    (hl : ∀ a : M, (1 : M) * a = a) (hr : ∀ a : M, a * (1 : M) = a) :
    defect M ≤ (Fintype.card M - 1) ^ 3 - (Fintype.card M - 1) ^ 2 := by
  classical
  -- the non-palindromic triples of `S` are all but the `|S|²` with first = last
  have hnonpal : ∀ {N : Type u} [DecidableEq N] (S : Finset N),
      ((S ×ˢ (S ×ˢ S)).filter fun t => t.1 ≠ t.2.2).card = S.card ^ 3 - S.card ^ 2 := by
    intro N _ S
    have htot : (S ×ˢ (S ×ˢ S)).card = S.card ^ 3 := by
      rw [Finset.card_product, Finset.card_product]; ring
    have heq : ((S ×ˢ (S ×ˢ S)).filter fun t => t.1 = t.2.2).card = S.card ^ 2 := by
      rw [Finset.card_filter, Finset.sum_product]
      have hinner : ∀ a ∈ S, (∑ p ∈ S ×ˢ S, if a = p.2 then 1 else 0) = S.card := by
        intro a ha
        rw [Finset.sum_product]
        have h1 : ∀ b ∈ S, (∑ c ∈ S, if a = c then 1 else 0) = 1 := by
          intro b _
          rw [Finset.sum_ite_eq S a (fun _ => 1), if_pos ha]
        rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one]
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
      ring
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := S ×ˢ (S ×ˢ S)) (p := fun t : N × N × N => t.1 ≠ t.2.2)
    simp only [not_not] at hsplit
    rw [htot, heq] at hsplit
    omega
  set S : Finset M := univ.erase 1 with hS
  have hSc : S.card = Fintype.card M - 1 := by
    rw [hS, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  -- a non-associative triple avoids the unit and is not a palindrome
  have hsub : defectSet M ⊆ (S ×ˢ (S ×ˢ S)).filter (fun t => t.1 ≠ t.2.2) := by
    intro t ht
    rw [defectSet, Finset.mem_filter] at ht
    obtain ⟨-, hne⟩ := ht
    have h1 : t.1 ≠ 1 := by
      intro h; exact hne (by rw [h, hl, hl])
    have h2 : t.2.1 ≠ 1 := by
      intro h; exact hne (by rw [h, hr, hl])
    have h3 : t.2.2 ≠ 1 := by
      intro h; exact hne (by rw [h, hr, hr])
    have h4 : t.1 ≠ t.2.2 := by
      intro h
      exact hne (by rw [← h, hcomm (t.1 * t.2.1) t.1, hcomm t.2.1 t.1])
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
    exact ⟨⟨Finset.mem_erase.mpr ⟨h1, Finset.mem_univ _⟩,
            Finset.mem_erase.mpr ⟨h2, Finset.mem_univ _⟩,
            Finset.mem_erase.mpr ⟨h3, Finset.mem_univ _⟩⟩, h4⟩
  calc defect M = (defectSet M).card := rfl
    _ ≤ ((S ×ˢ (S ×ˢ S)).filter (fun t => t.1 ≠ t.2.2)).card := Finset.card_le_card hsub
    _ = S.card ^ 3 - S.card ^ 2 := hnonpal S
    _ = (Fintype.card M - 1) ^ 3 - (Fintype.card M - 1) ^ 2 := by rw [hSc]
