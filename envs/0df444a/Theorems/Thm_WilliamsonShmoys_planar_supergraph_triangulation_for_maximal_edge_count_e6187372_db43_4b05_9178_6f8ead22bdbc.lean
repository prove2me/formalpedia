-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_for_maximal_edge_count_e6187372_db43_4b05_9178_6f8ead22bdbc
-- name    : WilliamsonShmoys.planar_supergraph_triangulation_for_maximal_edge_count_e6187372_db43_4b05_9178_6f8ead22bdbc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:42:16.404889+00:00
-- url     : https://prove2.me/theorems/4e7389f9-1e19-4f5b-8694-9853e59e8178
-- title:
--   Triangulated drawable supergraph on the same vertices
-- statement:
--   Every drawable finite simple graph on at least three fixed vertices is a subgraph of a drawable graph on those same vertices with exactly 3|V|−6 edges. The claim includes disconnected starting graphs and the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_triangulation_for_maximal_edge_count_e6187372_db43_4b05_9178_6f8ead22bdbc
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
