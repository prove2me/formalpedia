-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_edge_bound
-- name    : WilliamsonShmoys.planar_drawing_completion_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T06:44:04.162664+00:00
-- url     : https://prove2.me/theorems/47cfe247-f32d-4afb-b363-54161b3a97c2
-- title:
--   Edge bound for a planar drawing completion
-- statement:
--   Every drawable graph on at least three vertices has a drawable supergraph on the same vertex set with at least `3|V| - 6` edges. This packages the completion and planar Euler-bound argument needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_completion_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by sorry
