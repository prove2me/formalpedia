-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_induced_edge_bound_small
-- name    : WilliamsonShmoys.planar_connected_induced_edge_bound_small
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:37:05.611667+00:00
-- url     : https://prove2.me/theorems/a7c4dc5e-449a-45fa-b46e-8f114202752e
-- title:
--   Small induced simple graph edge bound
-- statement:
--   A nonempty induced subgraph on fewer than three vertices has at most half its vertex count in edges, using natural-number division. Connectedness and a drawing are unnecessary for this case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_induced_edge_bound_small
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (S : Finset V)
    (hNonempty : S.Nonempty)
    (hSmall : S.card < 3) :
    (H.induce (↑S : Set V)).edgeSet.ncard ≤ S.card / 2 := by sorry
