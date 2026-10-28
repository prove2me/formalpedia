-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_exists
-- name    : WilliamsonShmoys.maximal_drawable_supergraph_exists
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:32:18.226989+00:00
-- url     : https://prove2.me/theorems/cbcd6fc1-0feb-4ed5-bcb4-14b08ecc585b
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertex type that cannot be enlarged while remaining drawable.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_supergraph_exists
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists fun K : SimpleGraph V =>
      H <= K /\
      WilliamsonShmoys.HasPlanarDrawingOn K /\
      forall L : SimpleGraph V,
        K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K := by sorry
