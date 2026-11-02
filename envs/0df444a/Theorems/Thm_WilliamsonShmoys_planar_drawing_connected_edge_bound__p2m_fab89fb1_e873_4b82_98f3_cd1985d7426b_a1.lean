-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_edge_bound__p2m_fab89fb1_e873_4b82_98f3_cd1985d7426b_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_edge_bound__p2m_fab89fb1_e873_4b82_98f3_cd1985d7426b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:02:00.75507+00:00
-- url     : https://prove2.me/theorems/84071c7f-05d0-4d93-a512-f7a4506c6617
-- title:
--   Edge bound for a connected graph with a planar drawing
-- statement:
--   For a connected finite simple graph with at least three vertices, a drawing satisfying HasPlanarDrawingOn gives the standard Euler edge bound. Prove it by obtaining the plane embedding from the drawing, applying Euler’s formula, and using simplicity to bound face boundary lengths.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_edge_bound__p2m_fab89fb1_e873_4b82_98f3_cd1985d7426b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hConnected : K.Connected)
    (hPlanar : HasPlanarDrawingOn K) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    K.edgeFinset.card + 6 <= 3 * Fintype.card V := by sorry
