-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximum_edge_count_connected
-- name    : WilliamsonShmoys.planar_drawing_maximum_edge_count_connected
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T00:26:51.287433+00:00
-- url     : https://prove2.me/theorems/e27effe6-5950-4238-afe3-5630cdc86abe
-- title:
--   Equality in the planar edge bound forces connectedness
-- statement:
--   A drawable simple graph on at least three vertices with exactly `3|V|−6` edges is connected. The proof route is to apply the planar edge bound separately to its components; for components of size one or two use their direct edge bounds, and for larger components use Euler's planar bound. If there were at least two components, their total edge count would be strictly below `3|V|−6`. This converts the first child's numerical completion into the connected supergraph used by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximum_edge_count_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hEdges : (K.edgeSet.ncard : Int) =
      3 * (Fintype.card V : Int) - 6) :
    K.Connected := by sorry
