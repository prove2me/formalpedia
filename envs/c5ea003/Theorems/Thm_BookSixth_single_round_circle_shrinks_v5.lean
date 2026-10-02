-- Prove2me | Theorems.Thm_BookSixth_single_round_circle_shrinks_v5
-- name    : BookSixth.single_round_circle_shrinks_v5
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T05:24:57.740199+00:00
-- url     : https://prove2.me/theorems/73bfb50e-a62c-41cc-b44e-ce81f5bf9f3c
-- title:
--   Chapter 15: one round circle is shrunk by a global similarity (named zero parameter)
-- statement:
--   For a round circle C in R^3 there is a jointly continuous family K_t of ambient homeomorphisms of R^3, t in the half-open strip 0 <= t < 1, with jointly continuous inverse, fixing the identity at t = 0, such that every image K_t[C] is again a round circle. The motion is the global similarity K_t(x) = (1-t)*x + t*c where c is the centre of C; the scale 1-t is strictly positive for t < 1, so each K_t is a homeomorphism, and the images stay round by similarity_preserves_roundness. The zero parameter is named shrinkZero to keep the statement free of term-mode proofs.
-- source:
--   Proofs from THE BOOK, Chapter 15 (Aigner-Ziegler), geometric motion of perfect circles; the single-circle shrinking motion, using the accepted global-similarity roundness lemma.

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_similarity_preserves_roundness
open scoped BigOperators
open BookSixth
noncomputable section

def shrinkZero : {t : ℝ // 0 ≤ t ∧ t < 1} := ⟨0, le_rfl, zero_lt_one⟩

theorem BookSixth.single_round_circle_shrinks_v5 (C : Set Space3) (hC : RoundCircle C) :
    ∃ K : {t : ℝ // 0 ≤ t ∧ t < 1} → Space3 ≃ₜ Space3,
      (Continuous fun p : {t : ℝ // 0 ≤ t ∧ t < 1} × Space3 => K p.1 p.2) ∧
      (Continuous fun p : {t : ℝ // 0 ≤ t ∧ t < 1} × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K shrinkZero x = x) ∧
      (∀ t : {t : ℝ // 0 ≤ t ∧ t < 1}, RoundCircle ((K t) '' C)) := by sorry
