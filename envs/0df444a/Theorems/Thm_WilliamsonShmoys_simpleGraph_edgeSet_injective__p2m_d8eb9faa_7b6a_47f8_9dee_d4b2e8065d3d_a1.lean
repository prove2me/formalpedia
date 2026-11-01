-- Prove2me | Theorems.Thm_WilliamsonShmoys_simpleGraph_edgeSet_injective__p2m_d8eb9faa_7b6a_47f8_9dee_d4b2e8065d3d_a1
-- name    : WilliamsonShmoys.simpleGraph_edgeSet_injective__p2m_d8eb9faa_7b6a_47f8_9dee_d4b2e8065d3d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:30:30.396376+00:00
-- url     : https://prove2.me/theorems/7e422ede-7f55-49dc-a663-6c28d121d728
-- title:
--   A simple graph is determined by its edge set
-- statement:
--   Two simple graphs on the same vertex type with equal edge sets are equal. This makes edge-set inclusion a partial order on the finite carrier of graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.simpleGraph_edgeSet_injective__p2m_d8eb9faa_7b6a_47f8_9dee_d4b2e8065d3d_a1
    {V : Type} [Fintype V] [LinearOrder V] :
    Function.Injective (fun G : SimpleGraph V => G.edgeSet) := by sorry
