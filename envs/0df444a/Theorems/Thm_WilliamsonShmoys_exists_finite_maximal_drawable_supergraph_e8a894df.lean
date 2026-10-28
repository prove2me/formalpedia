-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_finite_maximal_drawable_supergraph_e8a894df
-- name    : WilliamsonShmoys.exists_finite_maximal_drawable_supergraph_e8a894df
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:34:53.668385+00:00
-- url     : https://prove2.me/theorems/1044848b-40cb-442b-a0cf-8e27ced539f1
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable simple graph on a finite vertex type has a drawable supergraph on that same type that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_finite_maximal_drawable_supergraph_e8a894df
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
