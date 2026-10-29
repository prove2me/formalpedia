-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_729fc1e5
-- name    : WilliamsonShmoys.planar_edge_upper_bound_729fc1e5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:06:44.856022+00:00
-- url     : https://prove2.me/theorems/c3c27980-9f1d-4b26-ac26-4100a7115914
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every drawable simple graph with at least three vertices has at most 3|V|−6 edges. This separates the Euler-counting obligation from the parent; a proof route is Euler’s formula with face-edge incidence counting, handling disconnected components and bridges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound_729fc1e5
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    R.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  sorry
