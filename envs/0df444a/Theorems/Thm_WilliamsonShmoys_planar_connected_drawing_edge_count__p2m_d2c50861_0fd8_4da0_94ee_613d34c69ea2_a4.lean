-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_drawing_edge_count__p2m_d2c50861_0fd8_4da0_94ee_613d34c69ea2_a4
-- name    : WilliamsonShmoys.planar_connected_drawing_edge_count__p2m_d2c50861_0fd8_4da0_94ee_613d34c69ea2_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:13:39.181406+00:00
-- url     : https://prove2.me/theorems/767b9b65-fd19-4cff-91fc-43d0a70ca1ea
-- title:
--   Edge bound for a connected planar drawing
-- statement:
--   Prove the topological core for a connected simple graph with at least three vertices. The drawing gives finitely many simple arcs whose distinct interiors do not intersect. Extract their cyclic orders at vertices, establish a finite planar embedding from the arcs using separation properties of simple curves, apply Euler's formula, and count face-edge incidences. Simplicity and the vertex lower bound handle the facial boundary cases. This removes the Euler and face-counting argument from the parent; it is the remaining substantive obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_drawing_edge_count__p2m_d2c50861_0fd8_4da0_94ee_613d34c69ea2_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hconn : G.Connected) (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    G.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
