-- Prove2me | Theorems.Thm_BookSixth_image_comp_preserves_roundness
-- name    : BookSixth.image_comp_preserves_roundness
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T18:08:37.233985+00:00
-- url     : https://prove2.me/theorems/6fd034d3-825f-4fcb-bcec-272fc5c4a2ee
-- title:
--   The image of a round circle under a composition of two maps is round
-- statement:
--   Let C be a subset of R^3 and let f and g be maps from R^3 to R^3. If the intermediate image f(g(C)) is a genuine round circle, then the direct image of C under the composition f composed with g is the same set and is therefore also a genuine round circle. This is the gluing principle behind every rigid-motion path used to standardise round circles: the accepted lemmas BookSixth.similarity_preserves_roundness, BookSixth.translation_preserves_roundness and the three rotation lemmas rotation_01, rotation_02 and rotation_12 each preserve roundness for one elementary step, and this lemma lets any finite composition of those steps be assembled without re-checking the orthonormal equations. The statement is purely about the set image and does not mention isotopies.
-- source:
--   Support lemma for BookSixth.perfect_circles_pairwise_unlinked_motion (Chapter 15, Theorem 1 of Aigner-Ziegler, Proofs from THE BOOK, sixth edition).

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.image_comp_preserves_roundness (f g : Space3 → Space3) (C : Set Space3)
    (hf : RoundCircle (f '' (g '' C))) :
    RoundCircle ((f ∘ g) '' C) := by sorry
