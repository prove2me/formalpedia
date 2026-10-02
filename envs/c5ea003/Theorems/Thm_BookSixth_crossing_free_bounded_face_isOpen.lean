-- Prove2me | Theorems.Thm_BookSixth_crossing_free_bounded_face_isOpen
-- name    : BookSixth.crossing_free_bounded_face_isOpen
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-24T06:46:34.553451+00:00
-- url     : https://prove2.me/theorems/6ddf3211-7860-4911-ac28-0c782b134a6c
-- title:
--   Crossing-free bounded face components are open
-- statement:
--   Every bounded connected component of the complement of a selected crossing-free continuous drawing support is open. The proved compact-support theorem makes the support closed, so its complement is open; local connectedness of the real plane then makes each connected component of that open complement open. This is a topological preparation for the later Euler and face-incidence arguments and does not assume those counts.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 45, Theorem 4, p. 317, https://doi.org/10.1007/978-3-662-57265-8_45. Topological bridge derived from the proved compact-support child BookSixth.crossing_free_support_compact (UUID 967a853d-2b6b-4930-9f68-abe9fbccb1ce) and the canonical definition of bounded complementary components.

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthCrossingFreeFaceData
import Theorems.Thm_BookSixth_crossing_free_support_compact
open BookSixth

theorem BookSixth.crossing_free_bounded_face_isOpen {N M : ℕ}
    (D : PlaneDrawing N M)
    (V : Finset (Fin N))
    (E : Finset (Fin M))
    {U : Set CrossingFreePlane}
    (hU : U ∈ crossingFreeBoundedFaces D V E) :
    IsOpen U := by sorry
