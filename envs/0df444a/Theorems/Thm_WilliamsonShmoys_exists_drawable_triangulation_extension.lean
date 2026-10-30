-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_triangulation_extension
-- name    : WilliamsonShmoys.exists_drawable_triangulation_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:01:22.609379+00:00
-- url     : https://prove2.me/theorems/2e4232c3-555d-4c5b-b73c-8a40e6547af5
-- title:
--   Every finite planar drawing extends to a triangulation
-- statement:
--   Every drawable graph on a finite ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices with exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_drawable_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hYdraw : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ Z : SimpleGraph V, Y ≤ Z ∧ WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      Z.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
