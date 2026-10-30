-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_augmentation_below_bound_v3
-- name    : WilliamsonShmoys.planar_drawing_edge_augmentation_below_bound_v3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:10:23.593644+00:00
-- url     : https://prove2.me/theorems/0dfabf1d-8f35-48fa-9b53-8c7a8f7b9c86
-- title:
--   Edge augmentation below the planar bound
-- statement:
--   If a drawable simple graph on at least three vertices has fewer than 3|V|−6 edges, it has a drawable strict supergraph on the same vertices with more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_augmentation_below_bound_v3
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hNdraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hbelow : N.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ K : SimpleGraph V, N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      N.edgeSet.ncard < K.edgeSet.ncard := by sorry
