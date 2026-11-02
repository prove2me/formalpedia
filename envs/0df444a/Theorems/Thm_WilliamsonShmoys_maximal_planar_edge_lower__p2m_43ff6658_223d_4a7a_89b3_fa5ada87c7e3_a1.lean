-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower__p2m_43ff6658_223d_4a7a_89b3_fa5ada87c7e3_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower__p2m_43ff6658_223d_4a7a_89b3_fa5ada87c7e3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:36:13.866695+00:00
-- url     : https://prove2.me/theorems/df5daf12-daf3-4429-a1d3-fb22e1c60853
-- title:
--   Lower bound for maximal drawable graphs
-- statement:
--   A graph maximal among drawable supergraphs on the same vertex set has at least 3|V|−6 edges. The classical route is to show maximality forces a triangulated planar embedding and then use Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower__p2m_43ff6658_223d_4a7a_89b3_fa5ada87c7e3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) [DecidableRel K.Adj],
      HasPlanarDrawingOn K → H ≤ K → K ≤ H) :
    3 * Fintype.card V ≤ H.edgeFinset.card + 6 := by sorry
