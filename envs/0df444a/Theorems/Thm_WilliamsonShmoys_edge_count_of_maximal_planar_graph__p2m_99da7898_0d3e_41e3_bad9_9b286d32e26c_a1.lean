-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_graph__p2m_99da7898_0d3e_41e3_bad9_9b286d32e26c_a1
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_graph__p2m_99da7898_0d3e_41e3_bad9_9b286d32e26c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:34:57.071479+00:00
-- url     : https://prove2.me/theorems/fc0abe73-fd21-4e9c-bb3c-f4df0112280b
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   An inclusion-maximal simple planar graph with at least three vertices has exactly 3|V|−6 edges. The standard proof route is to obtain a planar embedding from the drawing, show maximality forces connectedness and triangular faces, and combine Euler’s formula with face-edge incidence counting. The hypothesis 3 ≤ |V| is retained to cover the small boundary case |V|=3 and to support the extremal formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_count_of_maximal_planar_graph__p2m_99da7898_0d3e_41e3_bad9_9b286d32e26c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
      H.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
