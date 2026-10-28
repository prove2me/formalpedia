-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_finite_drawable_supergraph_maximal_by_inclusion
-- name    : WilliamsonShmoys.exists_finite_drawable_supergraph_maximal_by_inclusion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T12:04:31.149244+00:00
-- url     : https://prove2.me/theorems/85706daa-6274-4f1a-85f4-70c11c2da5bd
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs under inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_finite_drawable_supergraph_maximal_by_inclusion
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ M : SimpleGraph V,
      T ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M := by sorry
