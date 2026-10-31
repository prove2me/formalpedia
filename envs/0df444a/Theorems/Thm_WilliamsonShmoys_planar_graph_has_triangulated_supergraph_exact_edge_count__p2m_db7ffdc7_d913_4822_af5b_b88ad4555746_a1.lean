-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph_exact_edge_count__p2m_db7ffdc7_d913_4822_af5b_b88ad4555746_a1
-- name    : WilliamsonShmoys.planar_graph_has_triangulated_supergraph_exact_edge_count__p2m_db7ffdc7_d913_4822_af5b_b88ad4555746_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:57:08.277985+00:00
-- url     : https://prove2.me/theorems/7b41eed5-030c-4b58-a88f-053b0d647635
-- title:
--   Planar graph completion with exact edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices is a subgraph of a drawable graph on the same vertices with exactly $3|V|-6$ edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_triangulated_supergraph_exact_edge_count__p2m_db7ffdc7_d913_4822_af5b_b88ad4555746_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hL : HasPlanarDrawingOn L) : ∃ T : SimpleGraph V, L ≤ T ∧ HasPlanarDrawingOn T ∧ 3 * Fintype.card V - 6 = T.edgeSet.ncard := by sorry
