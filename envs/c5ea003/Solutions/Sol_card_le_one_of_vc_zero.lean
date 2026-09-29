-- Prove2me | solution 1 for card_le_one_of_vc_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:29:40.447461+00:00
-- url     : https://prove2.me/submissions/df7330e0-835d-4888-9bec-6efb79a36f46

-- Sol generated from Algebra/SauerShelah.lean
import Mathlib
import Definitions.Def_Algebra_SauerShelah

open Fin

/-! # CatalogBuild.Algebra.SauerShelah

Auto-generated from theorem catalog database.
Domain: Algebra
Declarations: 17
-/











-- ================================================================
--  Basic proj / embed API
-- ================================================================


























































theorem solution{n : ℕ} (F : Finset (Finset (Fin n)))
    (hF : ∀ A, Shatters F A → A.card ≤ 0) : F.card ≤ 1 := by
      contrapose! hF;
      -- Since F has more than one element, there exist S₁ ≠ S₂ ∈ F.
      obtain ⟨S₁, S₂, hS₁, hS₂, hne⟩ : ∃ S₁ S₂ : Finset (Fin n), S₁ ∈ F ∧ S₂ ∈ F ∧ S₁ ≠ S₂ := by
        exact?;
      -- Since S₁ ≠ S₂, there exists x with x ∈ S₁ and x ∉ S₂ (or vice versa), WLOG x ∈ S₁, x ∉ S₂.
      obtain ⟨x, hx₁, hx₂⟩ : ∃ x : Fin n, x ∈ S₁ ∧ x∉ S₂ ∨ x∉ S₁ ∧ x ∈ S₂ := by
        exact Classical.not_forall_not.1 fun h => hne <| Finset.ext fun x => by by_cases hx₁ : x ∈ S₁ <;> by_cases hx₂ : x ∈ S₂ <;> simpa [ hx₁, hx₂ ] using h x;
      · use {x};
        unfold Shatters; aesop;
      · use {x};
        unfold Shatters; aesop;
