-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_edge_maximal_planar__p2m_6b272625_9d5c_443e_9411_b56416706ef1_a1
-- name    : WilliamsonShmoys.edge_count_of_edge_maximal_planar__p2m_6b272625_9d5c_443e_9411_b56416706ef1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:30:50.135201+00:00
-- url     : https://prove2.me/theorems/1818e4a7-4acb-4ee2-9cf9-24cae947314c
-- title:
--   Edge count of an edge-maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no drawable strict edge-supergraph on the same vertex type has exactly 3|V|−6 edges. This child isolates the planar maximality and Euler-formula work from the finite extension argument. A proof route is to derive the triangulation property from edge-maximality for the given crossing-free drawing, apply the planar Euler formula, and count each edge along its incident triangular faces. The hypothesis |V| ≥ 3 is retained for the edge-count formula; at |V| = 3 it yields three edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_count_of_edge_maximal_planar__p2m_6b272625_9d5c_443e_9411_b56416706ef1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U)
    (hmax : ∀ (W : SimpleGraph V) (dW : DecidableRel W.Adj),
      HasPlanarDrawingOn W →
      (letI : DecidableRel U.Adj := dU
       letI : DecidableRel W.Adj := dW
       U.edgeFinset ⊆ W.edgeFinset) →
      (letI : DecidableRel U.Adj := dU
       letI : DecidableRel W.Adj := dW
       W.edgeFinset ⊆ U.edgeFinset))
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel U.Adj := dU
     U.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
