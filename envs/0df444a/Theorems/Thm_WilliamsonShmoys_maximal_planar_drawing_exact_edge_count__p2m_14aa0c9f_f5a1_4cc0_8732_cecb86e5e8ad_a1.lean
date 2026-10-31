-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count__p2m_14aa0c9f_f5a1_4cc0_8732_cecb86e5e8ad_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_14aa0c9f_f5a1_4cc0_8732_cecb86e5e8ad_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:38:12.540857+00:00
-- url     : https://prove2.me/theorems/517c01cd-00fc-45c6-9fdb-091b579590d9
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on a finite ordered vertex type with at least three vertices has exactly 3|V| - 6 edges. The standard route is to establish connectedness and triangular faces from maximality, then use Euler's formula and count face-edge incidences. The lower bound includes the three-vertex case, where maximality forces the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_14aa0c9f_f5a1_4cc0_8732_cecb86e5e8ad_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V)
    (hmax : forall H : SimpleGraph V, K <= H -> WilliamsonShmoys.HasPlanarDrawingOn H -> H <= K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
