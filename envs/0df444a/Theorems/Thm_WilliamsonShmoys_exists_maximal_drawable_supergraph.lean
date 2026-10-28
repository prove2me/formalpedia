-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:03:55.509275+00:00
-- url     : https://prove2.me/theorems/95ad1364-467e-4279-aede-848b881a92be
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in an inclusion maximal drawable graph on that same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L := by sorry
