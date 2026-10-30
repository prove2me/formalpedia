-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_card_upper_bound_connected
-- name    : WilliamsonShmoys.planar_drawing_edge_card_upper_bound_connected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:11:11.342572+00:00
-- url     : https://prove2.me/theorems/9ea0b94a-947d-48cd-be8b-8c01332ed453
-- title:
--   Edge bound for a connected planar drawing
-- statement:
--   A finite connected simple graph with the specified crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This isolates the Euler-counting argument, including conversion from the arc drawing to a plane map.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_card_upper_bound_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hCard : 3 ≤ Fintype.card V)
    (hConnected : S.Connected) :
    S.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
