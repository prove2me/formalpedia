-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_exists_maximal_extension
-- name    : WilliamsonShmoys.planar_drawingOn_exists_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:07:13.175516+00:00
-- url     : https://prove2.me/theorems/c6eab2ff-7135-4f60-93c6-339d6b211a41
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable simple graph on a finite vertex type has a drawable supergraph on the same vertices that is maximal under edge inclusion. There is no lower bound on the number of vertices, since this is a finite maximization argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_exists_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ K : SimpleGraph V,
      M.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn L →
        K.edgeSet ⊆ L.edgeSet →
        L.edgeSet ⊆ K.edgeSet := by sorry
