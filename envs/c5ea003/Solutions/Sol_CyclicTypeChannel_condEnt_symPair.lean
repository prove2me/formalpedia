-- Prove2me | solution 1 for CyclicTypeChannel.condEnt_symPair
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:25:56.505596+00:00
-- url     : https://prove2.me/submissions/bea7c7a9-b0a8-4c67-9819-0ef8285cb595

-- Sol generated from Shared/CyclicTypeChannelSymmetry.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelSymmetry
import Theorems.Thm_CyclicTypeChannel_uEnt_symPair
/-
# The which-factor wall is exactly zero

A semiprime `N = p q` presents its two prime factors symmetrically: nothing in
`N mod f` can say *which* factor carries which splitting type.  Experimentally
the "which-factor" information was measured at `0.0001` bits, i.e. zero.

This file proves that it is **exactly** zero, in complete generality:  for any
sample set carrying an involution `σ` which swaps the two components of the
read-out and fixes the conditioning variable, forgetting the order of the two
components changes both the entropy and the conditional entropy by *the same*
amount, namely the probability of an off-diagonal pair.  Consequently the
mutual information of the unordered read-out equals that of the ordered one.

The entropies themselves are genuinely different (the ordered pair carries
strictly more entropy whenever off-diagonal pairs occur); it is only the
*channel* that is insensitive to the ordering.
-/

open CyclicTypeChannel

open Finset


variable {α β : Type*} [LinearOrder β]



variable [DecidableEq β] {s : Finset α} {g : α → β × β} {σ : α → α}








open CyclicTypeChannel in
theorem solution{γ : Type*} [DecidableEq γ] {k : α → γ} (hσs : ∀ a ∈ s, σ a ∈ s)
    (hσσ : ∀ a ∈ s, σ (σ a) = a) (hgσ : ∀ a ∈ s, g (σ a) = ((g a).2, (g a).1))
    (hkσ : ∀ a ∈ s, k (σ a) = k a) :
    condEnt s (symPair ∘ g) k = condEnt s g k - (#{a ∈ s | (g a).1 ≠ (g a).2} : ℝ) / s.card := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [condEnt]
  have hN : (0 : ℝ) < s.card := by exact_mod_cast card_pos.2 hs
  have hterm : ∀ c ∈ s.image k,
      ((#{x ∈ s | k x = c} : ℝ) / s.card) * uEnt {x ∈ s | k x = c} (symPair ∘ g)
      = ((#{x ∈ s | k x = c} : ℝ) / s.card) * uEnt {x ∈ s | k x = c} g
        - (#{a ∈ ({x ∈ s | k x = c} : Finset α) | (g a).1 ≠ (g a).2} : ℝ) / s.card := by
    intro c hc
    have hne : ({x ∈ s | k x = c}).Nonempty := by
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hc
      exact ⟨a, by simp [ha]⟩
    have hNc : (0 : ℝ) < (#{x ∈ s | k x = c} : ℝ) := by exact_mod_cast card_pos.2 hne
    have h1 : ∀ a ∈ ({x ∈ s | k x = c} : Finset α), σ a ∈ ({x ∈ s | k x = c} : Finset α) := by
      intro a ha
      simp only [mem_filter] at ha ⊢
      exact ⟨hσs a ha.1, by rw [hkσ a ha.1, ha.2]⟩
    have h2 : ∀ a ∈ ({x ∈ s | k x = c} : Finset α), σ (σ a) = a :=
      fun a ha => hσσ a (mem_of_mem_filter a ha)
    have h3 : ∀ a ∈ ({x ∈ s | k x = c} : Finset α), g (σ a) = ((g a).2, (g a).1) :=
      fun a ha => hgσ a (mem_of_mem_filter a ha)
    rw [uEnt_symPair h1 h2 h3]
    field_simp
  rw [condEnt, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← condEnt, ← Finset.sum_div]
  congr 1
  congr 1
  have hfil : ∀ c, {a ∈ ({x ∈ s | k x = c} : Finset α) | (g a).1 ≠ (g a).2}
      = {x ∈ ({a ∈ s | (g a).1 ≠ (g a).2} : Finset α) | k x = c} := by
    intro c
    ext x
    simp only [mem_filter]
    tauto
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := k) (s := ({a ∈ s | (g a).1 ≠ (g a).2} : Finset α)) (t := s.image k)
    (fun x hx => mem_image_of_mem k (mem_of_mem_filter x hx))
  rw [show ∑ c ∈ s.image k, ((#{a ∈ ({x ∈ s | k x = c} : Finset α) | (g a).1 ≠ (g a).2} : ℕ) : ℝ)
      = ∑ c ∈ s.image k, ((#{x ∈ ({a ∈ s | (g a).1 ≠ (g a).2} : Finset α) | k x = c} : ℕ) : ℝ) from
    Finset.sum_congr rfl fun c _ => by rw [hfil c]]
  exact_mod_cast hfib.symm
