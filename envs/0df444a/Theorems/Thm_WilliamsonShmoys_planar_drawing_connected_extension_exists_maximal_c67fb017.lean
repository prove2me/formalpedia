-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_exists_maximal_c67fb017
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_exists_maximal_c67fb017
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:40:39.669643+00:00
-- url     : https://prove2.me/theorems/ce4084fe-b7db-4bc8-8e0b-a0bac8ec01d8
-- title:
--   Existence of a maximal drawn planar extension
-- statement:
--   Every finite graph with a drawing has a maximal drawn planar supergraph on the same vertices; that supergraph contains at least as many edges as the original.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_extension_exists_maximal_c67fb017
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      L ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard := by
  sorry
