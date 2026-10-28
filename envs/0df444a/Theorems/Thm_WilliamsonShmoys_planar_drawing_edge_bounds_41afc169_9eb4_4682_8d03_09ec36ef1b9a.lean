-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bounds_41afc169_9eb4_4682_8d03_09ec36ef1b9a
-- name    : WilliamsonShmoys.planar_drawing_edge_bounds_41afc169_9eb4_4682_8d03_09ec36ef1b9a
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T02:14:43.896405+00:00
-- url     : https://prove2.me/theorems/9a76f4a2-5658-436a-8a64-d2d1017687a1
-- title:
--   Connected planar drawing edge bounds
-- statement:
--   A connected finite simple graph with at least three vertices and a drawing satisfying the supplied crossing-free arc conditions has between n−1 and 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bounds_41afc169_9eb4_4682_8d03_09ec36ef1b9a
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : L.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Fintype.card V - 1 ≤ L.edgeSet.ncard ∧
      L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
