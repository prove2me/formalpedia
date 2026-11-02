-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_625bb0fc_e249_4e4e_ba10_71dd29d5fb91_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_625bb0fc_e249_4e4e_ba10_71dd29d5fb91_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:03:49.137859+00:00
-- url     : https://prove2.me/theorems/23fbcf6b-b479-4c5b-ac5b-aebde1c2012f
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph maximal among drawable supergraphs on the same vertex set, with at least three vertices, has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_625bb0fc_e249_4e4e_ba10_71dd29d5fb91_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hN : HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N)
    (hcard : 3 ≤ Fintype.card V) :
    6 * Fintype.card V = 2 * N.edgeFinset.card + 12 := by sorry
