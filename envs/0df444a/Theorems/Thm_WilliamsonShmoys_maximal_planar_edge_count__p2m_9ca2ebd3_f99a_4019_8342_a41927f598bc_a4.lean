-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_9ca2ebd3_f99a_4019_8342_a41927f598bc_a4
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_9ca2ebd3_f99a_4019_8342_a41927f598bc_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:59:44.695134+00:00
-- url     : https://prove2.me/theorems/2f6efb11-cffe-4335-a64a-833cc169dca5
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable finite simple graph on at least three vertices that is maximal under drawable edge extensions has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_9ca2ebd3_f99a_4019_8342_a41927f598bc_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ (L : SimpleGraph V) [DecidableRel L.Adj],
      HasPlanarDrawingOn L →
      K.edgeFinset ⊆ L.edgeFinset →
      K.edgeFinset = L.edgeFinset)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
