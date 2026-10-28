-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f_maximal_edge_lower_bound
-- name    : WilliamsonShmoys.planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f_maximal_edge_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T14:28:32.662076+00:00
-- url     : https://prove2.me/theorems/b05d0e4b-6b11-4adc-b313-dff8d769990a
-- title:
--   Maximal drawable graph has the triangulation edge count as a lower bound
-- statement:
--   A drawable graph that is maximal among drawable supergraphs on the same vertex type, with at least three vertices, has at least `3|V| − 6` edges. This removes the maximality-to-triangulation argument from the parent; a proof route is to establish connectedness and triangular face boundaries using maximality, then apply Euler’s formula and count edge-face incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f_maximal_edge_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V,
      T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) :
    3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by sorry
