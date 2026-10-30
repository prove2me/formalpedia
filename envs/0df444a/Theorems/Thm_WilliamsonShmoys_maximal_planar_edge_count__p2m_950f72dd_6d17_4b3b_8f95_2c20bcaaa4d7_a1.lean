-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_950f72dd_6d17_4b3b_8f95_2c20bcaaa4d7_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_950f72dd_6d17_4b3b_8f95_2c20bcaaa4d7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:29:30.555+00:00
-- url     : https://prove2.me/theorems/5de68fdf-7c57-4a5c-aa52-238846970023
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   A finite simple graph that is maximal among drawable supergraphs on its vertex set, with at least three vertices, has exactly 3|V|−6 edges. The boundary condition excludes smaller graphs, for which the formula need not hold. A proof route is to show maximality forces every face of a planar embedding to be triangular, then apply Euler’s formula and count each edge twice across face boundaries.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_950f72dd_6d17_4b3b_8f95_2c20bcaaa4d7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, LE.le H K ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> LE.le K H)
    (hV : LE.le 3 (Fintype.card V)) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
