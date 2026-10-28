-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_c10b408b_b7ec_40f0_b964_0a6697295590
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph_c10b408b_b7ec_40f0_b964_0a6697295590
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:11:06.673207+00:00
-- url     : https://prove2.me/theorems/9fc2ff8e-8eae-4277-87d2-af64225a3d3d
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable graph maximal among drawable supergraphs on that same vertex type. The result does not require a lower bound on the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph_c10b408b_b7ec_40f0_b964_0a6697295590
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
