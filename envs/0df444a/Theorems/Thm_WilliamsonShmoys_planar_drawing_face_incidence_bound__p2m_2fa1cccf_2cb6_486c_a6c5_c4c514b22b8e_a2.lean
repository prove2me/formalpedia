-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_incidence_bound__p2m_2fa1cccf_2cb6_486c_a6c5_c4c514b22b8e_a2
-- name    : WilliamsonShmoys.planar_drawing_face_incidence_bound__p2m_2fa1cccf_2cb6_486c_a6c5_c4c514b22b8e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:44:10.31487+00:00
-- url     : https://prove2.me/theorems/b3c9bfa4-c900-4902-b62c-e651fcb234b7
-- title:
--   Face-incidence bound for a planar drawing
-- statement:
--   For a connected simple graph on at least three vertices with the supplied planar drawing, any natural number satisfying its Euler equation obeys the face-incidence inequality. One proof route is to augment the graph to a maximal simple planar supergraph, use the planar edge bound E≤3V−6, and combine that bound with hEuler. Equivalently, count boundary-walk incidences, treating both sides of bridges separately. Three vertices excludes the small graph exceptions to the edge bound; connectedness and the drawing hypothesis are needed for the augmentation and incidence arguments.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_face_incidence_bound__p2m_2fa1cccf_2cb6_486c_a6c5_c4c514b22b8e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (faceCount : ℕ)
    (hEuler : Fintype.card V + faceCount = G.edgeSet.ncard + 2) :
    3 * faceCount <= 2 * G.edgeSet.ncard := by sorry
