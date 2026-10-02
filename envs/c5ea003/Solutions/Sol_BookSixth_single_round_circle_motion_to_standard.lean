-- Prove2me | solution 1 for BookSixth.single_round_circle_motion_to_standard
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T00:54:56.483773+00:00
-- url     : https://prove2.me/submissions/10c77d6f-26b8-43b7-bce0-a575e03372dd

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_standardizing_time_maps_are_similarities
import Theorems.Thm_BookSixth_roundness_of_rigid_similarity_isotopy
open scoped BigOperators
open BookSixth

noncomputable section

-- The `m = 1` case of `BookSixth.perfect_circles_pairwise_unlinked_motion`.
--
-- This is a pure composition of two already-`Proved` theorems and contains no
-- new mathematics.
--
-- `BookSixth.standardizing_time_maps_are_similarities` (`70d16099`) supplies,
-- for a round circle `D` and any index `k`, an ambient isotopy `H` from `id`
-- to a motion carrying `D` onto `standardCircle k`, such that every `H t` is a
-- positive Euclidean similarity on all of `Space3`.
--
-- `BookSixth.roundness_of_rigid_similarity_isotopy` (`7aa580d7`) turns exactly
-- that description of a family into roundness of every image of a round circle.
--
-- The two hypotheses differ only in the type ascription on the translation
-- vector `b` -- `Fin 3 → ℝ` in `70d16099` and `Space3` in `7aa580d7` -- and
-- `Space3` is an `abbrev` for `Fin 3 → ℝ` in `Definitions.Def_BookSixth`, so the
-- elaboration is by `exact` after instantiating `k := 0`.

theorem solution (D : Set Space3) (hD : RoundCircle D) :
    ∃ K : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => K p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K 0 x = x) ∧
      (K 1) '' D = standardCircle 0 ∧
      (∀ t, RoundCircle ((K t) '' D)) := by
  obtain ⟨H, hHcont, hHinv, hHzero, hHend, hHsim⟩ :=
    BookSixth.standardizing_time_maps_are_similarities D hD 0
  refine ⟨H, hHcont, hHinv, hHzero, hHend, ?_⟩
  exact BookSixth.roundness_of_rigid_similarity_isotopy hD H hHsim

end
