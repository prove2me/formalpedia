-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_34c1d13a_c463_44f3_a4ff_eb6476f05c93_a2
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_34c1d13a_c463_44f3_a4ff_eb6476f05c93_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:54:37.906603+00:00
-- url     : https://prove2.me/theorems/6400a378-148c-4107-bf45-1bb685620500
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   Every inclusion-maximal drawable simple graph on at least three vertices has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_34c1d13a_c463_44f3_a4ff_eb6476f05c93_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hT : HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U = T) :
    (letI : DecidableRel T.Adj := Classical.decRel T.Adj
     T.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
