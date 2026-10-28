-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_connectedification_retry3
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_connectedification_retry3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:10:00.345106+00:00
-- url     : https://prove2.me/theorems/edd78bbf-a461-4889-88a1-39b056b9319a
-- title:
--   Maximal drawable extension on a finite vertex set
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertices, with at least as many edges, that has no proper drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_connectedification_retry3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
