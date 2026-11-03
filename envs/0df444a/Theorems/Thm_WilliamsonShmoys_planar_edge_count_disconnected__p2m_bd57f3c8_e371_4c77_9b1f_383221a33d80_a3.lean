-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_disconnected__p2m_bd57f3c8_e371_4c77_9b1f_383221a33d80_a3
-- name    : WilliamsonShmoys.planar_edge_count_disconnected__p2m_bd57f3c8_e371_4c77_9b1f_383221a33d80_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:52:52.0372+00:00
-- url     : https://prove2.me/theorems/6875723b-f815-435e-a204-8de0d4b60ca9
-- title:
--   Planar edge bound for disconnected drawings
-- statement:
--   This is the disconnected case needed by the parent split, and it is independent of the connected child. It removes the disconnected branch’s edge-count obligation. A proof can join the drawing’s separate components with noncrossing arcs, then use Euler’s formula and triangular-face counting for the resulting connected planar supergraph and bound the original edges by containment. The hypothesis `|V| >= 3` is retained, including cases with isolated vertices or components of size two. The remaining core is constructing the planar joins and formalizing the embedding and face-count arguments from the arc data.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_disconnected__p2m_bd57f3c8_e371_4c77_9b1f_383221a33d80_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hdisconn : ¬ K.Connected)
    (hK : HasPlanarDrawingOn K) :
    letI : (L : SimpleGraph V) -> DecidableRel L.Adj :=
      fun L => Classical.decRel L.Adj
    K.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
