-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_3662a54d_ea7a_4ea3_804a_c2f8a32e2408_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_3662a54d_ea7a_4ea3_804a_c2f8a32e2408_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:46:30.601465+00:00
-- url     : https://prove2.me/theorems/1563787d-1e9d-4e0d-aca3-7df10f22af54
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An inclusion-maximal simple graph with a crossing-free drawing, connectedness, and at least three vertices has exactly 3n−6 edges. The proof route is to derive a plane embedding from the drawing, apply Euler’s formula, and use maximality to show every face is triangular.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_3662a54d_ea7a_4ea3_804a_c2f8a32e2408_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
