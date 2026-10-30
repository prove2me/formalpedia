-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_a3bf2761_3b00_45d2_af0e_a4c0f6d1919f
-- name    : WilliamsonShmoys.maximal_planar_edge_count_a3bf2761_3b00_45d2_af0e_a4c0f6d1919f
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:48:26.087806+00:00
-- url     : https://prove2.me/theorems/fcb16b3d-1c33-4f43-94c9-7021854a8873
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_a3bf2761_3b00_45d2_af0e_a4c0f6d1919f
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    (L.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
