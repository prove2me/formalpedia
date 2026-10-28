-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_drawing_extension
-- name    : WilliamsonShmoys.finite_maximal_planar_drawing_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:08:33.175819+00:00
-- url     : https://prove2.me/theorems/4e6cb4f1-22df-4e95-b487-ea7054718314
-- title:
--   Finite maximal planar drawing extension
-- statement:
--   Every finite graph with a planar drawing has a drawable supergraph on the same vertex type that is maximal under inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.finite_maximal_planar_drawing_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, L ≤ M →
          WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
