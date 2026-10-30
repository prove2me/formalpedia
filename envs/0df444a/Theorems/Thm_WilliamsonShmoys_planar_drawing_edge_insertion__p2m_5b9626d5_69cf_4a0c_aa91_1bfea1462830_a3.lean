-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_insertion__p2m_5b9626d5_69cf_4a0c_aa91_1bfea1462830_a3
-- name    : WilliamsonShmoys.planar_drawing_edge_insertion__p2m_5b9626d5_69cf_4a0c_aa91_1bfea1462830_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T10:04:06.274412+00:00
-- url     : https://prove2.me/theorems/dbc3254b-5f5b-4582-961f-6a369cb67369
-- title:
--   Insert an edge between distinct planar components
-- statement:
--   Adding an edge between unreachable vertices of a finitely drawn planar graph preserves the existence of a crossing-free drawing on the same vertex type. Non-reachability ensures the vertices are distinct and the edge was absent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_insertion__p2m_5b9626d5_69cf_4a0c_aa91_1bfea1462830_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (u v : V) (hnot : ¬ G.Reachable u v) :
    HasPlanarDrawingOn (G ⊔ SimpleGraph.edge u v) := by sorry
