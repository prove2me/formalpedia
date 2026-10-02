-- Prove2me | solution 1 for BookSixth.round_circle_snoc_of_transport
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T21:53:13.201138+00:00
-- url     : https://prove2.me/submissions/9e6238bb-6702-4e07-9dad-e0e1056645fd

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution {n : ℕ} (C : Fin n → Set Space3) (D : Set Space3)
    (H : ∃ K : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => K p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K 0 x = x) ∧
      (∀ i, (K 1) '' C i = standardCircle i.val) ∧
      (K 1) '' D = standardCircle n) :
    IsUnlink (Fin.snoc C D) := by
  obtain ⟨K, hK⟩ := H
  refine ⟨K, hK.1, hK.2.1, hK.2.2.1, ?_⟩
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hK.2.2.2.2
  · simpa using hK.2.2.2.1 j
