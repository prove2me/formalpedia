-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_2907dc87_c05a_4d84_a687_2b7bae17f05a
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_2907dc87_c05a_4d84_a687_2b7bae17f05a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:10:12.852656+00:00
-- url     : https://prove2.me/theorems/7408f5db-bde0-417a-91d0-eda442a3e522
-- title:
--   Extend a drawable graph to a maximal drawable supergraph
-- statement:
--   Every finite drawable simple graph is contained in a drawable supergraph maximal under edge inclusion, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_2907dc87_c05a_4d84_a687_2b7bae17f05a
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by sorry
