-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_877a68bf_2408_4570_9e48_0da03981c44d_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_877a68bf_2408_4570_9e48_0da03981c44d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:04:19.770697+00:00
-- url     : https://prove2.me/theorems/6f7b33c7-a7c9-44db-bbb3-dcbcd538e90d
-- title:
--   Edge maximality forces the planar extremal edge count
-- statement:
--   An edge-maximal graph with a crossing-free drawing and at least three vertices has at least 3|V| − 6 edges, stated as 3|V| ≤ |E| + 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_877a68bf_2408_4570_9e48_0da03981c44d_a1
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
     3 * Fintype.card V ≤ U.edgeFinset.card + 6) := by sorry
