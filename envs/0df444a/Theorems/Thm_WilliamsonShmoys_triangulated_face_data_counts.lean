-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulated_face_data_counts
-- name    : WilliamsonShmoys.triangulated_face_data_counts
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:14:41.426634+00:00
-- url     : https://prove2.me/theorems/11e0821a-f1ff-46d2-a22e-b664953cb58b
-- title:
--   Count incidences in triangulated face data
-- statement:
--   From finite face-edge data satisfying Euler’s equation, three incidences per face, two per edge, and agreement with the graph’s edge count, derive the two target equations by counting incident pairs in both orders.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangulatedPlanarFaceData

set_option autoImplicit false

theorem WilliamsonShmoys.triangulated_face_data_counts
    {V : Type} [Fintype V] [LinearOrder V]
    {H : SimpleGraph V}
    (D : WilliamsonShmoys.TriangulatedPlanarFaceData H) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f = 2 * H.edgeSet.ncard := by sorry
