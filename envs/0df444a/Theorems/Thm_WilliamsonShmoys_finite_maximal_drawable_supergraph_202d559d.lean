-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_supergraph_202d559d
-- name    : WilliamsonShmoys.finite_maximal_drawable_supergraph_202d559d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:49:29.307958+00:00
-- url     : https://prove2.me/theorems/cdc1e2d0-b721-4768-b7c3-0c6441169f9c
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   A drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_drawable_supergraph_202d559d
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
