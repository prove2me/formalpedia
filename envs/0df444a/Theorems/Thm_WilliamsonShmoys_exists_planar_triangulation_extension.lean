-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension
-- name    : WilliamsonShmoys.exists_planar_triangulation_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:38:21.334979+00:00
-- url     : https://prove2.me/theorems/9366ced6-dd71-48d9-aee0-ae0e36c1ee2c
-- title:
--   Extend a finite planar graph to a triangulation
-- statement:
--   Every finite graph with the given crossing-free drawing and at least three vertices has a planar supergraph on the same vertices whose faces can be triangulated and whose edge count is exactly 3n−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
