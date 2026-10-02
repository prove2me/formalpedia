-- Prove2me | solution 1 for BookSixth.single_round_circle_shrinks_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T03:36:36.393379+00:00
-- url     : https://prove2.me/submissions/8bbdba34-c76e-4638-b5e0-2240e446aab0

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_similarity_preserves_roundness
import Theorems.Thm_BookSixth_single_round_circle_shrinks_v9
open scoped BigOperators
open BookSixth

/-- **One round circle is shrunk by a global similarity, with the identity at time zero.**

This is `BookSixth.single_round_circle_shrinks_v9` with its identity condition
specialised to the zero time: `v9` proves the stronger statement that `K t0` is the
identity for *every* admissible time `t0` with `t0.1 = 0`, which in particular
supplies the case `t0 = ⟨0, by norm_num, by norm_num⟩` that this target names
explicitly. Everything else — forward continuity, joint continuity of the inverse,
and roundness of every intermediate image — is inherited unchanged.

The half-open time type `{t : ℝ // 0 ≤ t ∧ t < 1}` is deliberate. Canonical
shrinking has a zero-radius limit, which does not satisfy `RoundCircle`, so the
isotopy is built on the half-open interval and reparametrised onto a closed one
afterwards. -/
theorem solution (C : Set Space3) (hC : RoundCircle C) :
    ∃ K : {t : ℝ // 0 ≤ t ∧ t < 1} → Space3 ≃ₜ Space3,
      (Continuous fun p : {t : ℝ // 0 ≤ t ∧ t < 1} × Space3 => K p.1 p.2) ∧
      (Continuous fun p : {t : ℝ // 0 ≤ t ∧ t < 1} × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K ⟨0, by norm_num, by norm_num⟩ x = x) ∧
      (∀ t : {t : ℝ // 0 ≤ t ∧ t < 1}, RoundCircle ((K t) '' C)) := by
  obtain ⟨K, hcont, hsymm, hid, hround⟩ :=
    BookSixth.single_round_circle_shrinks_v9 C hC
  exact ⟨K, hcont, hsymm, hid ⟨0, by norm_num, by norm_num⟩ (by norm_num), hround⟩
