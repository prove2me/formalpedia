-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_extension__p2m_6b272625_9d5c_443e_9411_b56416706ef1_a1
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_6b272625_9d5c_443e_9411_b56416706ef1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:30:46.727034+00:00
-- url     : https://prove2.me/theorems/f4289382-c97c-4c13-a1b6-d7b29f8b93d9
-- title:
--   Existence of an edge-maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on that same type that is maximal among drawable supergraphs under edge inclusion. This child removes the finite maximization step from the parent. One proof route is to maximize edge count over the finite collection of simple graphs containing T whose drawing predicate holds; any drawable strict supergraph would have more edges. No lower bound on |V| is needed for this child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_6b272625_9d5c_443e_9411_b56416706ef1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (dT : DecidableRel T.Adj)
    (hT : HasPlanarDrawingOn T) :
    ∃ (U : SimpleGraph V) (dU : DecidableRel U.Adj),
      HasPlanarDrawingOn U ∧
      (letI : DecidableRel T.Adj := dT
       letI : DecidableRel U.Adj := dU
       T.edgeFinset ⊆ U.edgeFinset) ∧
      ∀ (W : SimpleGraph V) (dW : DecidableRel W.Adj),
        HasPlanarDrawingOn W →
        (letI : DecidableRel U.Adj := dU
         letI : DecidableRel W.Adj := dW
         U.edgeFinset ⊆ W.edgeFinset) →
        (letI : DecidableRel U.Adj := dU
         letI : DecidableRel W.Adj := dW
         W.edgeFinset ⊆ U.edgeFinset) := by sorry
