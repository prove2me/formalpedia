-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_card_upper_bound_disconnected
-- name    : WilliamsonShmoys.planar_drawing_edge_card_upper_bound_disconnected
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T16:19:55.440219+00:00
-- url     : https://prove2.me/theorems/984b85e4-975d-4113-b6a1-ecc4fb22400d
-- title:
--   Edge bound for a disconnected planar drawing
-- statement:
--   A finite disconnected simple graph with the specified crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This isolates restriction to connected components and the finite-sum argument, including components of size one or two.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_card_upper_bound_disconnected
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hCard : 3 ≤ Fintype.card V)
    (hNotConnected : ¬ S.Connected) :
    S.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
