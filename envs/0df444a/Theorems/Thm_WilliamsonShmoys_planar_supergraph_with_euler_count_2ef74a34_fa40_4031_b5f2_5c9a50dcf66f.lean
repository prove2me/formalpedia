-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f
-- name    : WilliamsonShmoys.planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:49:08.438256+00:00
-- url     : https://prove2.me/theorems/d17c59e9-0dcc-456e-9d55-ba4e611121c0
-- title:
--   Extend a finite planar graph to a planar graph with the Euler triangulation count
-- statement:
--   Every finite graph with at least three vertices and the packaged planar drawing extends on the same vertex type to a planar graph with the Euler triangulation edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ T : SimpleGraph V,
      K ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
        T.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
