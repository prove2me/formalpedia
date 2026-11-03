-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_1508a319_0bdf_43a6_9c8f_5ec7d4360d47_a2
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_1508a319_0bdf_43a6_9c8f_5ec7d4360d47_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:52:37.423758+00:00
-- url     : https://prove2.me/theorems/f922730b-ca22-4588-ba9a-35deaa5a3fb1
-- title:
--   Triangulation extension on the same vertex set
-- statement:
--   Any finite simply drawn planar graph on at least three vertices extends to a planar supergraph on the same vertex set with exactly 3n−6 edges. The required classical adjacency instance is installed locally for the edge count. A proof route is to extend the drawing to a maximal planar drawing, then use Euler’s formula; this also covers disconnected starting graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_1508a319_0bdf_43a6_9c8f_5ec7d4360d47_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hn : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel _
       H.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
