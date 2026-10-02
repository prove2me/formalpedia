-- Prove2me | Theorems.Thm_BookSixth_single_round_circle_motion_to_standard
-- name    : BookSixth.single_round_circle_motion_to_standard
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T00:50:08.488986+00:00
-- url     : https://prove2.me/theorems/9c911921-4e07-4155-a2fc-8dea456a6034
-- title:
--   A single round circle moves to the standard circle by a similarity isotopy that stays round
-- statement:
--   The `m = 1` case of `BookSixth.perfect_circles_pairwise_unlinked_motion` (`f6a7245e-187d-4a69-8b49-100cf7e4a1cc`).
--
--   Let `D` be a single round circle in `Space3 = Fin 3 → ℝ`. Then there is a family of ambient homeomorphisms `K : ℝ → Space3 ≃ₜ Space3` such that
--
--     * `K` and `K ⁻¹` are jointly continuous in `(t, x)`,
--     * `K 0 = id`,
--     * `K 1` sends `D` onto the standard circle `standardCircle 0`, and
--     * `(K t) '' D` is a round circle at every time `t`.
--
--   The last conjunct is the point of the target. It is what the parent leaf needs and what none of the accepted single-circle children delivers: `BookSixth.single_round_circle_shrinks_v9` (`145b1930`) only shrinks a circle towards its own centre on a *half-open* interval `[0, 1)` and never reaches a prescribed endpoint, whereas `BookSixth.standardizing_time_maps_are_similarities` (`70d16099`) reaches the prescribed endpoint but asserts roundness only through a separate hypothesis. This target combines the two.
--
--   No hypothesis of pairwise unlinking is needed, because for `m = 1` the parent's hypothesis `∀ i j, i ≠ j → IsUnlink (![C i, C j])` is vacuous: `Fin 1` has no two distinct indices. So this is exactly the base case of the parent's induction, and it is provable today from two already-`Proved` theorems.
-- source:
--   Two `Proved` theorems compose into this one with no new mathematics.
--
--   `BookSixth.standardizing_time_maps_are_similarities` (`70d16099`, accepted as candidate 3727, remote submission `5acf902c-5be1-4fa1-a12a-5c2b03f9ebc8`) states that for a round circle `D` and any `k : ℕ` there is `H : ℝ → Space3 ≃ₜ Space3` with both continuity legs, `H 0 = id`, `(H 1) '' D = standardCircle k`, and
--
--       (∀ t, ∃ A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ), ∃ a : ℝ, ∃ b : (Fin 3 → ℝ), 0 < a ∧
--         (∀ x y : (Fin 3 → ℝ), (∑ i, (A x) i * (A y) i) = ∑ i, x i * y i) ∧
--         (∀ x : (Fin 3 → ℝ), H t x = a • (A x) + b))
--
--   `BookSixth.roundness_of_rigid_similarity_isotopy` (`7aa580d7`) states that for a round `C` and a family `G` satisfying
--
--       (∀ t, ∃ A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ), ∃ a : ℝ, ∃ b : Space3, 0 < a ∧
--         (∀ x y : Space3, (∑ i, (A x) i * (A y) i) = ∑ i, x i * y i) ∧
--         (∀ x : Space3, (G t) x = a • (A x) + b))
--
--   one gets `∀ t, RoundCircle ((G t) '' C)`. The two hypotheses are the same modulo the type ascription on `b`, which is `Space3 = Fin 3 → ℝ` in both cases and hence the same type by `abbrev`; the instantiation is by `exact`, or by `simpa` if elaboration needs the abbreviation unfolded.
--
--   So: instantiate `70d16099` at `(D, hD, k := 0)`, take its `H` as `K`, and feed its last conjunct to `7aa580d7` at `C := D`. The first four conjuncts of the goal are `70d16099`'s first three conjuncts together with its endpoint clause at `k = 0`; the fifth is `7aa580d7`'s conclusion.
--
--   The reason this target is worth separating from the parent is diagnostic rather than algebraic: the parent additionally needs the family-level `IsUnlink C` from pairwise hypotheses, which is the separate Open target `BookSixth.round_circle_unlink` (`2468ff3e`). Isolating the `m = 1` case shows that the roundness half of the leaf is fully discharged by the existing toolkit, so the residue is purely the unlink-gluing problem.

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_standardizing_time_maps_are_similarities
import Theorems.Thm_BookSixth_roundness_of_rigid_similarity_isotopy
open scoped BigOperators
open BookSixth

theorem BookSixth.single_round_circle_motion_to_standard (D : Set Space3)
    (hD : RoundCircle D) :
    ∃ K : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => K p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K 0 x = x) ∧
      (K 1) '' D = standardCircle 0 ∧
      (∀ t, RoundCircle ((K t) '' D)) := by sorry
