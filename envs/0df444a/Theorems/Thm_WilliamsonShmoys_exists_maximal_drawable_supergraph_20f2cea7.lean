-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_20f2cea7
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_20f2cea7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:10:43.102752+00:00
-- url     : https://prove2.me/theorems/d1dc9a81-eb89-4489-86b0-8f335c8976d7
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable simple graph on a fixed finite vertex set has a drawable supergraph that has no strictly larger drawable supergraph on that vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_20f2cea7
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
