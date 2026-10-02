-- Prove2me | Theorems.Thm_BookSixth_roundness_compose_two_general
-- name    : BookSixth.roundness_compose_two_general
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-25T18:49:46.158995+00:00
-- url     : https://prove2.me/theorems/b298bbf3-4b40-4805-9a44-ee0ad4d17a34
-- title:
--   Composing two roundness-preserving motions preserves roundness at every time
-- statement:
--   Let C be a set, and let G and L be two families of homeomorphisms of R^3 indexed by real time. Suppose that at every time each of them maps C to a genuine round circle. Then at every time the composed motion that first applies L and then G also maps C to a genuine round circle. This is the fully general gluing statement for roundness: the accepted lemma BookSixth.roundness_compose_two requires the outer motion G to be a pure positive similarity, which is too restrictive to assemble the rigid motion of BookSixth.round_circle_single_standardize, since that motion is a composition of rotations, a positive exponential scaling and a translation. With this lemma, any finite composition of roundness-preserving motions is roundness preserving at every time, which is the ingredient the Chapter 15, Theorem 1 obligation forall t, RoundCircle ((K t) '' C i) requires.
-- source:
--   Support lemma for BookSixth.perfect_circles_pairwise_unlinked_motion (Chapter 15, Theorem 1 of Aigner-Ziegler, Proofs from THE BOOK, sixth edition).

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.roundness_compose_two_general {C : Set Space3}
    (G : ℝ → Space3 ≃ₜ Space3) (hGround : ∀ t, RoundCircle ((G t) '' C))
    (L : ℝ → Space3 ≃ₜ Space3) (hLround : ∀ t, RoundCircle ((L t) '' C)) :
    ∀ t, RoundCircle ((fun s => G t (L t s)) '' C) := by sorry
