-- Prove2me | solution 1 for BookSixth.single_round_circle_shrinks_v4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T01:49:24.073582+00:00
-- url     : https://prove2.me/submissions/aa633eb6-d5e4-4386-8ec5-af0375e1b303

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_similarity_preserves_roundness
import Theorems.Thm_BookSixth_single_round_circle_shrinks_v9
open scoped BigOperators
open BookSixth

theorem solution (C : Set Space3) (hC : RoundCircle C) :
    ∃ K : {t : ℝ // 0 ≤ t ∧ t < 1} → Space3 ≃ₜ Space3,
      (Continuous fun p : {t : ℝ // 0 ≤ t ∧ t < 1} × Space3 => K p.1 p.2) ∧
      (Continuous fun p : {t : ℝ // 0 ≤ t ∧ t < 1} × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K ⟨0, le_rfl, zero_lt_one⟩ x = x) ∧
      (∀ t : {t : ℝ // 0 ≤ t ∧ t < 1}, RoundCircle ((K t) '' C)) := by
  obtain ⟨K, h1, h2, hzero, hround⟩ :=
    BookSixth.single_round_circle_shrinks_v9 C hC
  refine ⟨K, h1, h2, ?_, hround⟩
  intro x
  exact hzero _ rfl x
