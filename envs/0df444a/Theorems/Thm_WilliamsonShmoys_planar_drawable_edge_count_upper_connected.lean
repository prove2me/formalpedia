-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_count_upper_connected
-- name    : WilliamsonShmoys.planar_drawable_edge_count_upper_connected
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:58:10.927989+00:00
-- url     : https://prove2.me/theorems/8814d45e-d622-431a-b932-563855d5cf21
-- title:
--   Upper edge bound for a connected drawable graph
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has at most 3|V| − 6 edges. This isolates the Euler and face-incidence count. A proof can derive a planar embedding from the connected drawing, apply Euler’s formula, and count edge incidences around faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_edge_count_upper_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hconn : K.Connected) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
