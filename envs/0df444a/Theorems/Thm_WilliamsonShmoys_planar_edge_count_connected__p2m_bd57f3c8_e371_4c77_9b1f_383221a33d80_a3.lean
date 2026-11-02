-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_connected__p2m_bd57f3c8_e371_4c77_9b1f_383221a33d80_a3
-- name    : WilliamsonShmoys.planar_edge_count_connected__p2m_bd57f3c8_e371_4c77_9b1f_383221a33d80_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:52:48.608221+00:00
-- url     : https://prove2.me/theorems/e2583d82-96a1-4ed4-8709-65222159201c
-- title:
--   Planar edge bound for connected drawings
-- statement:
--   This is the connected case needed by the parent split. It removes the connected branch’s edge-count obligation. Prove it from the drawing by constructing a plane embedding, applying Euler’s formula and triangular-face counting after maximal completion, and using edge containment. The `|V| >= 3` condition handles the small-vertex boundary where the usual triangular-face argument needs its nondegenerate case. The remaining core is formalizing the embedding and face counts from the arc data.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_connected__p2m_bd57f3c8_e371_4c77_9b1f_383221a33d80_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : K.Connected)
    (hK : HasPlanarDrawingOn K) :
    letI : (L : SimpleGraph V) -> DecidableRel L.Adj :=
      fun L => Classical.decRel L.Adj
    K.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
