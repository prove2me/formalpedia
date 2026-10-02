-- Prove2me | Theorems.Thm_BookSixth_single_round_circle_shrinks_v9
-- name    : BookSixth.single_round_circle_shrinks_v9
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T06:10:25.029986+00:00
-- url     : https://prove2.me/theorems/145b1930-7383-4b46-9be5-17b38fffd5ea
-- title:
--   Chapter 15: one round circle is shrunk by a global similarity (parser-safe zero-time clause)
-- statement:
--   For a round circle C in R^3 there is a jointly continuous family K_t of ambient homeomorphisms of R^3, t in the half-open strip 0 <= t < 1, with jointly continuous inverse, equal to the identity at the zero time, and such that every image K_t[C] is again a round circle. The motion is the global similarity K_t(x) = (1-t)*x + t*c where c is the centre of C; the scale 1-t is strictly positive for t < 1 (BookSixth.shrinking_similarity_scale_positive, now Proved), so each K_t is a homeomorphism, and the images stay round by similarity_preserves_roundness. The zero-time clause is stated as 'for every t0 in the strip with t0 = 0' rather than by writing the zero element as a literal, because the platform's target parser rejects proof terms in the subtype's value positions. This is equivalent: t0.1 = 0 determines t0 uniquely by Subtype.ext, and the strip is inhabited at 0, so the clause is not vacuous and is not a weakening.
-- source:
--   Proofs from THE BOOK, Chapter 15 (Aigner-Ziegler), geometric motion of perfect circles; the single-circle shrinking motion, using the accepted global-similarity roundness lemma.

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_similarity_preserves_roundness
open scoped BigOperators
open BookSixth

theorem BookSixth.single_round_circle_shrinks_v9 (C : Set Space3) (hC : RoundCircle C) :
    ∃ K : {t : ℝ // 0 ≤ t ∧ t < 1} → Space3 ≃ₜ Space3,
      (Continuous fun p : {t : ℝ // 0 ≤ t ∧ t < 1} × Space3 => K p.1 p.2) ∧
      (Continuous fun p : {t : ℝ // 0 ≤ t ∧ t < 1} × Space3 => (K p.1).symm p.2) ∧
      (∀ t0 : {t : ℝ // 0 ≤ t ∧ t < 1}, t0.1 = 0 → ∀ x, K t0 x = x) ∧
      (∀ t : {t : ℝ // 0 ≤ t ∧ t < 1}, RoundCircle ((K t) '' C)) := by sorry
