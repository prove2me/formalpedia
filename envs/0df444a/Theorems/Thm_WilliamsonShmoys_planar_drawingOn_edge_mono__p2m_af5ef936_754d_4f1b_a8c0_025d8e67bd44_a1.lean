-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_mono__p2m_af5ef936_754d_4f1b_a8c0_025d8e67bd44_a1
-- name    : WilliamsonShmoys.planar_drawingOn_edge_mono__p2m_af5ef936_754d_4f1b_a8c0_025d8e67bd44_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:40:22.700758+00:00
-- url     : https://prove2.me/theorems/4c1c20b6-4b09-456a-9c27-0ba6603a8696
-- title:
--   Planar drawing is preserved under taking subgraphs
-- statement:
--   If one graph's edge set is contained in another's, any crossing-free drawing of the larger graph is a crossing-free drawing of the smaller graph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawingOn_edge_mono__p2m_af5ef936_754d_4f1b_a8c0_025d8e67bd44_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G.edgeSet ⊆ H.edgeSet)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
