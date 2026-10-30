-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f_triangulation_count
-- name    : WilliamsonShmoys.planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f_triangulation_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:07:40.587345+00:00
-- url     : https://prove2.me/theorems/4775edbd-82ef-459b-aadf-0a529107c00e
-- title:
--   Maximal planar graphs have the Euler triangulation edge count
-- statement:
--   An inclusion-maximal simple graph with the packaged planar drawing and at least three vertices has exactly `3|V| − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f_triangulation_count
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V,
      T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) :
    T.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
