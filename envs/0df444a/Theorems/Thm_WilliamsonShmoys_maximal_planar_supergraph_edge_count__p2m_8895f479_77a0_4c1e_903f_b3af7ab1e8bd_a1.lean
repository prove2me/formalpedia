-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count__p2m_8895f479_77a0_4c1e_903f_b3af7ab1e8bd_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_8895f479_77a0_4c1e_903f_b3af7ab1e8bd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T12:46:15.308642+00:00
-- url     : https://prove2.me/theorems/d800a379-5df5-4e36-a12d-7e3e08fd9483
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no strict drawable supergraph on the same vertices has exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_8895f479_77a0_4c1e_903f_b3af7ab1e8bd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeSet = L.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
