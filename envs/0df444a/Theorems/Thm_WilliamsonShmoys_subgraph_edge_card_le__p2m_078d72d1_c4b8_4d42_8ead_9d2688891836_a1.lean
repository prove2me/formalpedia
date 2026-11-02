-- Prove2me | Theorems.Thm_WilliamsonShmoys_subgraph_edge_card_le__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1
-- name    : WilliamsonShmoys.subgraph_edge_card_le__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:42:38.050177+00:00
-- url     : https://prove2.me/theorems/7085ece2-035b-4fb4-afb8-ee84c5dd3ba2
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite graphs on the same vertex type, inclusion of graphs implies that the first graph’s edge count is no larger than the second’s.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.subgraph_edge_card_le__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1 {V : Type} [Fintype V] [LinearOrder V] (G F : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel F.Adj] (hGF : G <= F) : G.edgeFinset.card <= F.edgeFinset.card := by sorry
