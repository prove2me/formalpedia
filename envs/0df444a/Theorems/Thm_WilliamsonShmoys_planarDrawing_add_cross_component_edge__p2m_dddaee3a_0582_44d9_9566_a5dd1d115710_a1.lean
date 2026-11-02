-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_add_cross_component_edge__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a1
-- name    : WilliamsonShmoys.planarDrawing_add_cross_component_edge__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T12:29:23.461206+00:00
-- url     : https://prove2.me/theorems/889652c1-a82f-462e-b8d8-8391a5f102fc
-- title:
--   Add a drawable edge between distinct components
-- statement:
--   Given a finite disconnected graph with a crossing-free drawing, find vertices in different connected components and add exactly the edge between them while retaining a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_add_cross_component_edge__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hdisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v ∧
      ∃ H : SimpleGraph V,
        G ≤ H ∧
        H.edgeSet = G.edgeSet ∪ {Sym2.mk u v} ∧
        WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
