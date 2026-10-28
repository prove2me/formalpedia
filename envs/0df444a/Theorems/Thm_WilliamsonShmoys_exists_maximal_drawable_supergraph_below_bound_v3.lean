-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_below_bound_v3
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_below_bound_v3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:45:11.957556+00:00
-- url     : https://prove2.me/theorems/3f9c0e0f-1ec5-4fce-a5e1-4b41d741f3cd
-- title:
--   Finite maximal drawable supergraph for the edge-bound reduction
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_below_bound_v3
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hNdraw : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
