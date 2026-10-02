-- Prove2me | Theorems.Thm_BookSixth_crossing_free_support_compact
-- name    : BookSixth.crossing_free_support_compact
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T22:53:57.090193+00:00
-- url     : https://prove2.me/theorems/967a853d-2b6b-4930-9f68-abe9fbccb1ce
-- title:
--   Compactness of a selected continuous drawing support
-- statement:
--   For a finite drawing, the support formed by finitely many selected vertices and the images of finitely many continuous edge arcs is compact. Each edge image is compact by continuity, and the finite union of the selected vertex and edge images is compact. This fact supports the later planar-face construction but does not assume an Euler formula or a finite face-incidence theorem.
-- source:
--   Compactness adapter for the crossing-free face construction in Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 45, Theorem 4, p. 317, https://doi.org/10.1007/978-3-662-57265-8_45, using the canonical Prove2Me drawing definition b1fcef2b-61fb-4326-bde6-cb6070d37c77.

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthCrossingFreeFaceData
open BookSixth

theorem BookSixth.crossing_free_support_compact {N M : ℕ}
    (D : PlaneDrawing N M) (V : Finset (Fin N)) (E : Finset (Fin M)) :
    IsCompact (crossingFreeSupport D V E) := by sorry
