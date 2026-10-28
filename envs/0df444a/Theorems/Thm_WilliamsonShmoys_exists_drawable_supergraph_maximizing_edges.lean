-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_maximizing_edges
-- name    : WilliamsonShmoys.exists_drawable_supergraph_maximizing_edges
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T20:14:08.042081+00:00
-- url     : https://prove2.me/theorems/2a741e24-f66a-4993-9075-f32f7c502b84
-- title:
--   Existence of a drawable supergraph with maximal edge count
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph maximal under inclusion among drawable graphs on that vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_drawable_supergraph_maximizing_edges
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by sorry
