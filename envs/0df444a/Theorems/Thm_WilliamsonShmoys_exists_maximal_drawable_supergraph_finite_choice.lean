-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_finite_choice
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_finite_choice
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:38:44.548001+00:00
-- url     : https://prove2.me/theorems/e43e894e-648c-4dc2-b251-44712043d11d
-- title:
--   A drawable graph has a maximal drawable supergraph by finite choice
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in an inclusion-maximal drawable graph on that same type. Choose a drawable supergraph containing H with the largest edge count; finiteness of V makes the candidate family finite and H makes it nonempty. No lower bound on the vertex count is needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_finite_choice
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
