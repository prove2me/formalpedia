-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_edge_bound
-- name    : WilliamsonShmoys.planar_completion_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T14:02:37.001974+00:00
-- url     : https://prove2.me/theorems/13d363ce-212c-434e-9c01-93b0b95d2ef0
-- title:
--   Planar completion at the triangulation edge bound
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly the triangulation edge bound number of edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V,
      J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
