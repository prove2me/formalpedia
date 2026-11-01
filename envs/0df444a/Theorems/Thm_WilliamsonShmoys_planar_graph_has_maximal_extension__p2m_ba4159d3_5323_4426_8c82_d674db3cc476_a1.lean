-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_maximal_extension__p2m_ba4159d3_5323_4426_8c82_d674db3cc476_a1
-- name    : WilliamsonShmoys.planar_graph_has_maximal_extension__p2m_ba4159d3_5323_4426_8c82_d674db3cc476_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:01:34.707658+00:00
-- url     : https://prove2.me/theorems/2303d053-5855-4c64-93f3-04af828a3544
-- title:
--   Extend a drawable graph to a planar graph with maximum edge count
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex set has a drawable supergraph on the same vertex set whose edge count is the maximum possible planar edge count: the complete-graph count for at most two vertices, and 3|V|−6 otherwise.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_maximal_extension__p2m_ba4159d3_5323_4426_8c82_d674db3cc476_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      HasPlanarDrawingOn H ∧ G ≤ H ∧
        H.edgeFinset.card =
          if Fintype.card V ≤ 2 then
            Fintype.card V * (Fintype.card V - 1) / 2
          else 3 * Fintype.card V - 6 := by sorry
