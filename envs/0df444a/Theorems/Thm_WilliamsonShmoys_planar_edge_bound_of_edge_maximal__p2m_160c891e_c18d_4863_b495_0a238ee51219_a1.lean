-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_edge_maximal__p2m_160c891e_c18d_4863_b495_0a238ee51219_a1
-- name    : WilliamsonShmoys.planar_edge_bound_of_edge_maximal__p2m_160c891e_c18d_4863_b495_0a238ee51219_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:00:41.440392+00:00
-- url     : https://prove2.me/theorems/b9887391-36ac-4b13-9489-3daf1e406adb
-- title:
--   Edge bound for maximal drawable graphs
-- statement:
--   A drawable simple graph on at least three vertices that maximizes edge count among its drawable supergraphs has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound_of_edge_maximal__p2m_160c891e_c18d_4863_b495_0a238ee51219_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K →
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : Fintype ↑K.edgeSet := Fintype.ofFinite _
       letI : DecidableRel N.Adj := Classical.decRel N.Adj
       letI : Fintype ↑N.edgeSet := Fintype.ofFinite _
       K.edgeFinset.card ≤ N.edgeFinset.card)) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     letI : Fintype ↑N.edgeSet := Fintype.ofFinite _
     3 * Fintype.card V ≤ N.edgeFinset.card + 6) := by
  sorry
