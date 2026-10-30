-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_card_upper_bound_connected__p2m_984b85e4_975d_4113_b6a1_ecc4fb22400d_a3
-- name    : WilliamsonShmoys.planar_drawing_edge_card_upper_bound_connected__p2m_984b85e4_975d_4113_b6a1_ecc4fb22400d_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:32:36.241978+00:00
-- url     : https://prove2.me/theorems/6e32d747-02e1-49b2-b405-bee4fbe18965
-- title:
--   Edge bound for a connected planar drawing
-- statement:
--   A connected simple graph on at least three vertices with the specified crossing-free drawing has at most `3|V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_card_upper_bound_connected__p2m_984b85e4_975d_4113_b6a1_ecc4fb22400d_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hCard : 3 ≤ Fintype.card V)
    (hConnected : S.Connected) :
    S.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
