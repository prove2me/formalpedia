-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edgeMaximal_planar_supergraph
-- name    : WilliamsonShmoys.exists_edgeMaximal_planar_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:03:14.32786+00:00
-- url     : https://prove2.me/theorems/fd6d40b7-1393-46fb-a133-1b9285bc25cb
-- title:
--   Choose an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has an inclusion-maximal drawable supergraph on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_edgeMaximal_planar_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V,
          L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
