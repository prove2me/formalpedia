-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_44d3f95a_e4af_4a94_b096_ba30239a3f07
-- name    : WilliamsonShmoys.planar_maximal_extension_44d3f95a_e4af_4a94_b096_ba30239a3f07
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:58:09.648912+00:00
-- url     : https://prove2.me/theorems/7318c3e4-8b9f-4e44-84ef-e8cb4cffa2cb
-- title:
--   Extend a finite drawable graph to an edge-maximal drawable graph
-- statement:
--   A drawable simple graph on this finite ordered vertex type is contained in an edge-maximal drawable graph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_extension_44d3f95a_e4af_4a94_b096_ba30239a3f07
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        (∀ K : SimpleGraph V,
          H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) := by
  sorry
