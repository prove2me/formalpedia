-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_exists_8d131a4d
-- name    : WilliamsonShmoys.maximal_drawable_supergraph_exists_8d131a4d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:22:49.607281+00:00
-- url     : https://prove2.me/theorems/aeb6a1b0-5a8d-4203-95ef-aff4927be2ea
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has an inclusion-maximal drawable supergraph on the same vertices, with at least as many edges. Prove existence by taking a maximal element among the finite collection of drawable supergraphs; edge-count monotonicity follows from inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_supergraph_exists_8d131a4d
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn N) :
    ∃ H : SimpleGraph V,
      N ≤ H ∧
      HasPlanarDrawingOn H ∧
      (N.edgeSet.ncard : Int) ≤ (H.edgeSet.ncard : Int) ∧
      (∀ M : SimpleGraph V, H ≤ M → HasPlanarDrawingOn M → M ≤ H) := by sorry
