-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_extension_exists
-- name    : WilliamsonShmoys.maximal_planar_drawing_extension_exists
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:21:10.285816+00:00
-- url     : https://prove2.me/theorems/1651d78b-9a7d-4f81-b0ae-7c5a6c7a375d
-- title:
--   A planar drawing has a maximal planar extension
-- statement:
--   Every finite graph with a planar drawing has a planar supergraph on the same vertex type that has no strictly larger planar supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_extension_exists
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V, M ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
