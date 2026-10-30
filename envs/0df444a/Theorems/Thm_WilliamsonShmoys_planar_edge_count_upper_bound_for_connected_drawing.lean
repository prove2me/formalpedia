-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_for_connected_drawing
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_for_connected_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:57:28.841521+00:00
-- url     : https://prove2.me/theorems/f46eb32c-8748-42d0-90df-c18adb9d23dd
-- title:
--   Edge bound for a connected graph with the supplied drawing
-- statement:
--   For a connected graph with at least three vertices, establish the planar edge bound from the supplied arc drawing. This isolates the topological core used by the parent. An independent proof route is to derive the plane embedding’s facial boundary walks from the drawing, apply Euler’s formula, count incidences so every edge contributes twice to the total face-boundary length, and use simplicity to bound facial lengths below by three, treating degenerate small facial walks explicitly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound_for_connected_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
