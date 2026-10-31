-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_has_exact_edge_count__p2m_c94121e2_adc9_4018_a433_d3dee737ddb5_a1
-- name    : WilliamsonShmoys.edge_maximal_planar_graph_has_exact_edge_count__p2m_c94121e2_adc9_4018_a433_d3dee737ddb5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:09:53.767+00:00
-- url     : https://prove2.me/theorems/60b38c6b-3179-48fe-bb14-f21b6e8b7c6f
-- title:
--   An edge-maximal planar graph has the maximal planar edge count
-- statement:
--   A drawable simple graph on at least three vertices that has no strict drawable supergraph on the same vertex set has exactly 3|V|−6 edges. The hypotheses include the boundary case |V| = 3, where maximality forces the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_graph_has_exact_edge_count__p2m_c94121e2_adc9_4018_a433_d3dee737ddb5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
