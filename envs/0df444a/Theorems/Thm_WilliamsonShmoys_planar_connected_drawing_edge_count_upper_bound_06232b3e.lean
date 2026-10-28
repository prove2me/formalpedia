-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_drawing_edge_count_upper_bound_06232b3e
-- name    : WilliamsonShmoys.planar_connected_drawing_edge_count_upper_bound_06232b3e
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:14:42.406982+00:00
-- url     : https://prove2.me/theorems/47b65748-ca34-425c-87e9-ebcae4108beb
-- title:
--   Edge-count bound for connected planar drawings
-- statement:
--   A connected finite simple graph with a planar drawing and at least three vertices has at most 3|V|−6 edges. The three-vertex boundary is included; the triangle realizes equality. The independent proof route is Euler’s formula for the connected drawing and a count showing every face has at least three edge-sides. This child carries the main planar counting obligation left after augmentation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_drawing_edge_count_upper_bound_06232b3e
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hConnected : L.Connected)
    (hDrawing : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
