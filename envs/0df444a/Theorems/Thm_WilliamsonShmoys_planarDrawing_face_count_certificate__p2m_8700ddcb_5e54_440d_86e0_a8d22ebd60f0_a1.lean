-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_face_count_certificate__p2m_8700ddcb_5e54_440d_86e0_a8d22ebd60f0_a1
-- name    : WilliamsonShmoys.planarDrawing_face_count_certificate__p2m_8700ddcb_5e54_440d_86e0_a8d22ebd60f0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:35:30.430426+00:00
-- url     : https://prove2.me/theorems/9ee3cdb6-314f-4644-806d-ad6bf91ebce3
-- title:
--   Face count certificate for a connected planar drawing
-- statement:
--   For a connected simple graph with at least three vertices and a crossing-free drawing, the faces have boundary-walk lengths whose sum is twice the edge count, each length is at least three, and the vertex, face, and edge counts satisfy Euler's relation. Boundary walks count edge sides with multiplicity, so bridges contribute both darts even when both sides border the same face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_face_count_certificate__p2m_8700ddcb_5e54_440d_86e0_a8d22ebd60f0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : Nat, ∃ faceLength : Fin f → Nat,
      Fintype.card V + f =
          (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2 ∧
        (∑ i : Fin f, faceLength i) =
          2 * (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) ∧
        ∀ i : Fin f, 3 ≤ faceLength i := by sorry
