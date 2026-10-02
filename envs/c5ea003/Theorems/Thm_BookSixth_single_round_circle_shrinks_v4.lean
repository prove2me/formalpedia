-- Prove2me | Theorems.Thm_BookSixth_single_round_circle_shrinks_v4
-- name    : BookSixth.single_round_circle_shrinks_v4
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T05:07:31.093898+00:00
-- url     : https://prove2.me/theorems/b01869c5-134f-4d25-8bbb-700a40ec75b4
-- title:
--   Chapter 15: one round circle is shrunk by a global similarity (parse-safe endpoint)
-- statement:
--   For a round circle C in R^3 there is a jointly continuous family K_t of ambient homeomorphisms of R^3, t in [0,1), with jointly continuous inverse, K_0 the identity, such that every image K_t[C] is again a round circle. The motion is the global similarity K_t(x) = (1-t)*x + t*c, where c is the centre of C; its scale 1-t is strictly positive for t<1, so each K_t is a homeomorphism.
-- source:
--   Proofs from THE BOOK, Chapter 15 (Aigner-Ziegler), geometric motion of perfect circles; the single-circle shrinking motion, using the accepted global-similarity roundness lemma.

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_similarity_preserves_roundness
open scoped BigOperators
open BookSixth

theorem BookSixth.single_round_circle_shrinks_v4 (C : Set Space3) (hC : RoundCircle C) :
    ∃ K : {t : ℝ // 0 ≤ t ∧ t < 1} → Space3 ≃ₜ Space3,
      (Continuous fun p : {t : ℝ // 0 ≤ t ∧ t < 1} × Space3 => K p.1 p.2) ∧
      (Continuous fun p : {t : ℝ // 0 ≤ t ∧ t < 1} × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K ⟨0, le_rfl, zero_lt_one⟩ x = x) ∧
      (∀ t : {t : ℝ // 0 ≤ t ∧ t < 1}, RoundCircle ((K t) '' C)) := by sorry
