-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_6cde29f9_0337_48f4_829a_b67e3b72f2a9_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_6cde29f9_0337_48f4_829a_b67e3b72f2a9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:13:39.741436+00:00
-- url     : https://prove2.me/theorems/0869a5fc-4e7b-4b4a-9c67-2dc00ff9ed2f
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on a finite ordered vertex type with at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_6cde29f9_0337_48f4_829a_b67e3b72f2a9_a1 {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hU : HasPlanarDrawingOn U)
    (hmax : ∀ W : SimpleGraph V, U.edgeSet ⊆ W.edgeSet →
      HasPlanarDrawingOn W → U.edgeSet = W.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
