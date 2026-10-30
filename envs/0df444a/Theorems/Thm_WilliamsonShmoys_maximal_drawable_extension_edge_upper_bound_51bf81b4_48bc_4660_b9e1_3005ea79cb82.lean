-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension_edge_upper_bound_51bf81b4_48bc_4660_b9e1_3005ea79cb82
-- name    : WilliamsonShmoys.maximal_drawable_extension_edge_upper_bound_51bf81b4_48bc_4660_b9e1_3005ea79cb82
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:15:57.715507+00:00
-- url     : https://prove2.me/theorems/81565f28-e6bf-499b-a9cb-e936b0a27170
-- title:
--   Planar simple graph edge upper bound for a drawable extension
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_extension_edge_upper_bound_51bf81b4_48bc_4660_b9e1_3005ea79cb82
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
