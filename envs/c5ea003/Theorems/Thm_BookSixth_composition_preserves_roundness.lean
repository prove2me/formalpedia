-- Prove2me | Theorems.Thm_BookSixth_composition_preserves_roundness
-- name    : BookSixth.composition_preserves_roundness
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T17:51:09.270605+00:00
-- url     : https://prove2.me/theorems/98ad40ac-489b-43b6-b999-a963f884a1c0
-- title:
--   A composition of two maps preserves a round circle if the intermediate image is round
-- statement:
--   Let C be a set, and let f and g be maps from R^3 to R^3. If the intermediate image f(g(C)) is a genuine round circle, then the direct image (f composed with g)(C) is exactly the same set, so it is a genuine round circle as well. This is the gluing principle behind every rigid-motion path used to standardise round circles: the accepted lemmas BookSixth.similarity_preserves_roundness, BookSixth.translation_preserves_roundness and the three rotation lemmas rotation_01, rotation_02 and rotation_12 each preserve roundness for one elementary step, and this lemma lets any finite composition of those steps be assembled without re-checking the orthonormal equations. The statement is purely about the set image and does not mention isotopies.
-- source:
--   Support lemma for BookSixth.perfect_circles_pairwise_unlinked_motion (Chapter 15, Theorem 1 of Aigner-Ziegler, Proofs from THE BOOK, sixth edition).

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.composition_preserves_roundness {α : Type*} (f g : Space3 → Space3)
    (C : Set Space3) (hf : RoundCircle (f '' (g '' C))) :
    RoundCircle ((fun x : Space3 => f (g x)) '' C) := by sorry
