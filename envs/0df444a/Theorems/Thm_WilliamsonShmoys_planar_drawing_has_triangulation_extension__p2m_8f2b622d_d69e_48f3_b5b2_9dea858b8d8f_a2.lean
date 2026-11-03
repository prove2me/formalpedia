-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_extension__p2m_8f2b622d_d69e_48f3_b5b2_9dea858b8d8f_a2
-- name    : WilliamsonShmoys.planar_drawing_has_triangulation_extension__p2m_8f2b622d_d69e_48f3_b5b2_9dea858b8d8f_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:51:53.589334+00:00
-- url     : https://prove2.me/theorems/584708af-d974-4efc-b22f-05859fd9ba8d
-- title:
--   Planar drawing has a triangulation extension
-- statement:
--   Every finite simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn has an extension on the same vertex type that also has such a drawing and exactly 3|V|−6 edges, while retaining all original edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_triangulation_extension__p2m_8f2b622d_d69e_48f3_b5b2_9dea858b8d8f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
        H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
