-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_connected_drawingOn_282b0fbb
-- name    : WilliamsonShmoys.planar_edge_count_connected_drawingOn_282b0fbb
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:06:45.40457+00:00
-- url     : https://prove2.me/theorems/3772fefb-1039-4ea0-9393-dafce3569b64
-- title:
--   Connected planar drawing edge bound
-- statement:
--   A connected finite simple graph with at least three vertices and a drawing satisfying `HasPlanarDrawingOn` has at most `3|V| - 6` edges. The proof route is to obtain a combinatorial embedding from the drawing, apply Euler’s formula, and show each facial boundary walk has length at least three, counting bridge sides with multiplicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_edge_count_connected_drawingOn_282b0fbb
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V)
    (hConnected : L.Connected) :
    (L.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by sorry
