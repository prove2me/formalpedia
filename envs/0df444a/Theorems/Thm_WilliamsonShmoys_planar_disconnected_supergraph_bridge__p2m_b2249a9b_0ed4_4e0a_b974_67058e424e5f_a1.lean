-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_supergraph_bridge__p2m_b2249a9b_0ed4_4e0a_b974_67058e424e5f_a1
-- name    : WilliamsonShmoys.planar_disconnected_supergraph_bridge__p2m_b2249a9b_0ed4_4e0a_b974_67058e424e5f_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-31T21:45:01.297748+00:00
-- url     : https://prove2.me/theorems/70a1b3ee-3cfa-4fc7-a9eb-9c28f3782b43
-- title:
--   Planar disconnected graph has a bridge extension
-- statement:
--   Every finite disconnected graph with a crossing-free drawing has a crossing-free supergraph containing an edge between two vertices that were in different connected components. No lower bound on the number of vertices is needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_disconnected_supergraph_bridge__p2m_b2249a9b_0ed4_4e0a_b974_67058e424e5f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G)
    (hdis : ¬ G.Connected) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v := by sorry
