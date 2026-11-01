-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_card_le_max__p2m_ba4159d3_5323_4426_8c82_d674db3cc476_a1
-- name    : WilliamsonShmoys.planar_edge_card_le_max__p2m_ba4159d3_5323_4426_8c82_d674db3cc476_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:01:38.159574+00:00
-- url     : https://prove2.me/theorems/e846f25e-f357-4ee7-96c9-c2f0a093ea71
-- title:
--   Planar graphs satisfy the maximum edge bound
-- statement:
--   A graph with a crossing-free drawing on a finite ordered vertex set has at most the complete-graph edge count when there are at most two vertices, and at most 3|V|−6 edges otherwise.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_card_le_max__p2m_ba4159d3_5323_4426_8c82_d674db3cc476_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) :
    G.edgeFinset.card ≤
      if Fintype.card V ≤ 2 then
        Fintype.card V * (Fintype.card V - 1) / 2
      else 3 * Fintype.card V - 6 := by sorry
