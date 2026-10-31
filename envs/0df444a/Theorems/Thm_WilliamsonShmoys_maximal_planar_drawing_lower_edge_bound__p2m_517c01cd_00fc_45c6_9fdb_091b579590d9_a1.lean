-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_lower_edge_bound__p2m_517c01cd_00fc_45c6_9fdb_091b579590d9_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_lower_edge_bound__p2m_517c01cd_00fc_45c6_9fdb_091b579590d9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:49:06.015645+00:00
-- url     : https://prove2.me/theorems/64a4f4fc-6559-4890-9561-6e7d9fc3f1e0
-- title:
--   Lower edge bound for an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least 3|V| − 6 edges. The three-vertex boundary case is covered: maximality forces all three possible edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_lower_edge_bound__p2m_517c01cd_00fc_45c6_9fdb_091b579590d9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V)
    (hmax : forall H : SimpleGraph V, K <= H -> WilliamsonShmoys.HasPlanarDrawingOn H -> H <= K) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  sorry
