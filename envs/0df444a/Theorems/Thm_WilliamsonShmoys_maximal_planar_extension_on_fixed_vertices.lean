-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_on_fixed_vertices
-- name    : WilliamsonShmoys.maximal_planar_extension_on_fixed_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:19:30.562336+00:00
-- url     : https://prove2.me/theorems/1c77427f-8989-4fc7-8b20-aab206ff1d4b
-- title:
--   Finite maximal planar supergraph extension on fixed vertices
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type has an inclusion-maximal planar supergraph on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension_on_fixed_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ M : SimpleGraph V,
      U ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ X : SimpleGraph V,
        M ≤ X → WilliamsonShmoys.HasPlanarDrawingOn X → X ≤ M := by sorry
