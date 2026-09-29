-- Prove2me | solution 1 for CyclicTypeChannel.uEnt_symPair
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:24:09.497205+00:00
-- url     : https://prove2.me/submissions/9df7e04d-06bd-4865-9570-006746cb30e6

-- Sol generated from Shared/CyclicTypeChannelSymmetry.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelSymmetry
import Theorems.Thm_CyclicTypeChannel_card_symPair_fiber
import Theorems.Thm_CyclicTypeChannel_fiber_card_pos
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
theorem solution(hσs : ∀ a ∈ s, σ a ∈ s) (hσσ : ∀ a ∈ s, σ (σ a) = a)
    (hgσ : ∀ a ∈ s, g (σ a) = ((g a).2, (g a).1)) :
    uEnt s (symPair ∘ g) = uEnt s g - (#{a ∈ s | (g a).1 ≠ (g a).2} : ℝ) / s.card := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [uEnt]
  have hN : (0 : ℝ) < s.card := by exact_mod_cast card_pos.2 hs
  have hterm : ∀ a ∈ s, Real.logb 2 (#{x ∈ s | (symPair ∘ g) x = (symPair ∘ g) a} : ℝ)
      = Real.logb 2 (#{x ∈ s | g x = g a} : ℝ) + (if (g a).1 ≠ (g a).2 then (1 : ℝ) else 0) := by
    intro a ha
    have hpos : (0 : ℝ) < (#{x ∈ s | g x = g a} : ℝ) := by exact_mod_cast fiber_card_pos ha
    have hcard := card_symPair_fiber hσs hσσ hgσ a
    by_cases hd : (g a).1 = (g a).2
    · rw [hcard, if_pos hd, if_neg (by simpa using hd)]
      simp
    · rw [hcard, if_neg hd, if_pos hd]
      push_cast
      rw [Real.logb_mul (by norm_num) (ne_of_gt hpos),
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      ring
  have hcount : ∑ a ∈ s, (if (g a).1 ≠ (g a).2 then (1 : ℝ) else 0)
      = (#{a ∈ s | (g a).1 ≠ (g a).2} : ℝ) := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, nsmul_eq_mul, mul_one, add_zero]
  rw [uEnt, uEnt, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hcount]
  field_simp
  ring
