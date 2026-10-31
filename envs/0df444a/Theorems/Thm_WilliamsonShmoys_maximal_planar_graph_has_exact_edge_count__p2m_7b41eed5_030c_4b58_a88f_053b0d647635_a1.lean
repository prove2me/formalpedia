-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_exact_edge_count__p2m_7b41eed5_030c_4b58_a88f_053b0d647635_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_7b41eed5_030c_4b58_a88f_053b0d647635_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:01:14.868898+00:00
-- url     : https://prove2.me/theorems/0cd2651d-edaf-48bf-b0c6-7823a1c2bf88
-- title:
--   An inclusion-maximal drawable graph has the triangulated edge count
-- statement:
--   A drawable finite simple graph on at least three vertices that is maximal under edge inclusion among drawable graphs has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_7b41eed5_030c_4b58_a88f_053b0d647635_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : HasPlanarDrawingOn T) (hmax : ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U ≤ T) : 3 * Fintype.card V - 6 = T.edgeSet.ncard := by sorry
