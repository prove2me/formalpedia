-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ConeVerifier.badDirection_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:05:51.309208+00:00
-- url     : https://prove2.me/submissions/48c33c5c-cd33-45c3-b4df-65bef984d1f4

import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_search_correct
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_faceRows_iff

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
open FourierMotzkin
namespace Kourovka.MetabelianEnumeration.ConeVerifier
theorem _root_.solution {n : ℕ} (supports : Supports n) (epsilon : ℚ) :
    badDirection supports epsilon = true ↔
      ∃ x : Fin n → ℝ, CubeSphere x ∧
        ∀ support ∈ supports, ∃ u ∈ support, dot u x ≤ epsilon := by
  simp only [badDirection, List.any_eq_true, List.mem_finRange, true_and,
    search_correct, faceRows_iff]
  constructor
  · rintro ⟨i, sign, hsign, x, ⟨hx, hc⟩, hs⟩
    refine ⟨x, ⟨hc, i, ?_⟩, hs⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hsign
    rcases hsign with rfl | rfl
    · exact Or.inl (by simpa using hx)
    · exact Or.inr (by simpa using hx)
  · rintro ⟨x, ⟨hc, i, hi⟩, hs⟩
    rcases hi with hi | hi
    · exact ⟨i, -1, by simp, x, ⟨by simpa using hi, hc⟩, hs⟩
    · exact ⟨i, 1, by simp, x, ⟨by simpa using hi, hc⟩, hs⟩
end Kourovka.MetabelianEnumeration.ConeVerifier
