-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_finite_maximality
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_finite_maximality
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:45:42.623643+00:00
-- url     : https://prove2.me/theorems/fcf2393b-324a-42ab-9e7a-edf9978e09bc
-- title:
--   A maximal planar supergraph exists by finite maximality
-- statement:
--   Every graph with a planar drawing on a finite ordered vertex type has a same-vertex planar supergraph maximal under edge inclusion. This removes the maximality-selection step from the parent. Independently, consider the finite family of edge sets of planar supergraphs containing M and choose one of maximum cardinality; any strict supergraph has more edges, so it cannot remain planar.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_finite_maximality
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        ∀ P : SimpleGraph V, N ≤ P →
          WilliamsonShmoys.HasPlanarDrawingOn P → P = N := by sorry
