-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_completion_eb003b3d_a492_4a49_92ea_fad95e296393
-- name    : WilliamsonShmoys.maximal_planar_edge_completion_eb003b3d_a492_4a49_92ea_fad95e296393
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:55:37.892454+00:00
-- url     : https://prove2.me/theorems/17116a12-3e08-4cdd-9e5e-221cdff470e7
-- title:
--   Complete a drawable graph to the maximal planar edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex type with exactly `3 * card V - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_completion_eb003b3d_a492_4a49_92ea_fad95e296393
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H' : SimpleGraph V,
      H ≤ H' ∧ WilliamsonShmoys.HasPlanarDrawingOn H' ∧
        H'.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
