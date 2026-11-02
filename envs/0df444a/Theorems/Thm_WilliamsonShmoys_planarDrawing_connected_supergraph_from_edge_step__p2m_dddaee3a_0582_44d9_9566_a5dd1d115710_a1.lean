-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_connected_supergraph_from_edge_step__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a1
-- name    : WilliamsonShmoys.planarDrawing_connected_supergraph_from_edge_step__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:29:25.176704+00:00
-- url     : https://prove2.me/theorems/aa9f8502-788d-4376-8cf6-48061960ef49
-- title:
--   Iterate planar cross-component edge extensions
-- statement:
--   If each disconnected planar graph on the given finite vertex type admits a planar extension by one edge between distinct components, then iterating that step produces a connected planar supergraph of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_connected_supergraph_from_edge_step__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hn : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hstep : ∀ G : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn G →
      ¬ G.Connected →
      ∃ u v : V, ¬ G.Reachable u v ∧
        ∃ H : SimpleGraph V,
          G ≤ H ∧
          H.edgeSet = G.edgeSet ∪ {Sym2.mk u v} ∧
          WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
