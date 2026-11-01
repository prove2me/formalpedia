-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_bridge_between_unreachable_vertices__p2m_30445ffc_ee20_477d_a948_c780081d704c_a1
-- name    : WilliamsonShmoys.planar_drawing_add_bridge_between_unreachable_vertices__p2m_30445ffc_ee20_477d_a948_c780081d704c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:37:34.39085+00:00
-- url     : https://prove2.me/theorems/8d306757-503b-48cb-97e7-90978e85f379
-- title:
--   Add a planar bridge between unreachable vertices
-- statement:
--   Given a planar drawing and two unreachable vertices, add an edge between those vertices while retaining all existing edges and a planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_add_bridge_between_unreachable_vertices__p2m_30445ffc_ee20_477d_a948_c780081d704c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hplanar : HasPlanarDrawingOn K)
    (u v : V) (hnot : ¬ K.Reachable u v) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      L.Adj u v ∧
      HasPlanarDrawingOn L := by sorry
