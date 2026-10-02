-- Prove2me | Theorems.Thm_BookSixth_roundness_compose_on_intermediate
-- name    : BookSixth.roundness_compose_on_intermediate
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T18:56:43.799284+00:00
-- url     : https://prove2.me/theorems/73e62463-d160-408f-96df-31f7d714b415
-- title:
--   Roundness of the composed image follows from roundness of the intermediate image
-- statement:
--   Let C be a set, and let G and L be two families of homeomorphisms of R^3 indexed by real time. Suppose that at every time the composed image obtained by first applying L and then G is a genuine round circle. Then at every time the composed image is again a genuine round circle, written directly as the image of C under the pointwise composition. This is the set-theoretic identity underlying any gluing of roundness-preserving motions: the image of C under G t composed with L t is exactly the image of the intermediate set (L t) applied to C under G t, so roundness of the intermediate image is precisely what is needed. It is the correct generalisation of the accepted lemma BookSixth.roundness_compose_two, whose hypothesis that the outer motion is a pure positive similarity is unnecessarily strong and cannot be applied to the rigid motion built in BookSixth.round_circle_single_standardize.
-- source:
--   Support lemma for BookSixth.perfect_circles_pairwise_unlinked_motion (Chapter 15, Theorem 1 of Aigner-Ziegler, Proofs from THE BOOK, sixth edition).

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.roundness_compose_on_intermediate {C : Set Space3}
    (G : ℝ → Space3 ≃ₜ Space3) (L : ℝ → Space3 ≃ₜ Space3)
    (hGround : ∀ t, RoundCircle ((G t) '' ((L t) '' C))) :
    ∀ t, RoundCircle ((fun s => G t (L t s)) '' C) := by sorry
