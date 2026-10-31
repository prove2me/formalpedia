-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_subgraph__p2m_67118cd4_2aed_4d90_82ea_b0a7807bb269_a1
-- name    : WilliamsonShmoys.planar_drawingOn_subgraph__p2m_67118cd4_2aed_4d90_82ea_b0a7807bb269_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:52:46.55253+00:00
-- url     : https://prove2.me/theorems/d5ee1dfe-09fa-4b82-a5b5-e18e835d5c41
-- title:
--   Planar drawings are inherited by subgraphs
-- statement:
--   If a graph has a crossing-free drawing, every graph on the same vertices whose edges are a subset also has such a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawingOn_subgraph__p2m_67118cd4_2aed_4d90_82ea_b0a7807bb269_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hHG : H.edgeSet ⊆ G.edgeSet)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
