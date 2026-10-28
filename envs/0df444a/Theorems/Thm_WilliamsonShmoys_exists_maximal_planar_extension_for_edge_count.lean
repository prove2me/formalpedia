-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_for_edge_count
-- name    : WilliamsonShmoys.exists_maximal_planar_extension_for_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:22:02.204077+00:00
-- url     : https://prove2.me/theorems/61165bf4-be59-4a18-b3cc-cfdd5fef5b12
-- title:
--   A maximal planar supergraph exists on the same vertices
-- statement:
--   Every graph with the specified planar drawing is contained in an inclusion-maximal graph with such a drawing on the same finite vertex type. The proof route is to maximize edge count among the finite collection of planar supergraphs; inclusion maximality follows because a strict supergraph has more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_extension_for_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L ≤ K := by sorry
