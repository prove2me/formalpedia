-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation__p2m_6400a378_148c_4107_bf45_1bb685620500_a2
-- name    : WilliamsonShmoys.planar_edge_augmentation__p2m_6400a378_148c_4107_bf45_1bb685620500_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:48:40.86157+00:00
-- url     : https://prove2.me/theorems/e3fcbf10-6f41-4741-b7a4-cf721019c4f7
-- title:
--   Augmenting a planar drawing below the triangulation bound
-- statement:
--   If a graph with the specified drawing has strictly fewer than three times the number of vertices minus six edges, then it has a strict drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_augmentation__p2m_6400a378_148c_4107_bf45_1bb685620500_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hT : HasPlanarDrawingOn T) :
    (letI : DecidableRel T.Adj := Classical.decRel T.Adj
     T.edgeFinset.card < 3 * Fintype.card V - 6 →
       ∃ U : SimpleGraph V, T ≤ U ∧ U ≠ T ∧ HasPlanarDrawingOn U) := by sorry
