-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_connected_triangulation_extension_1bb3a12b
-- name    : WilliamsonShmoys.maximal_planar_edge_count_for_connected_triangulation_extension_1bb3a12b
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T18:02:42.885543+00:00
-- url     : https://prove2.me/theorems/d6e88113-94a3-49d5-a584-31d3c8b36e15
-- title:
--   Edge count of a maximal planar drawing in the triangulation extension
-- statement:
--   A connected drawable graph on at least three vertices that maximizes edge count among its drawable supergraphs has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_for_connected_triangulation_extension_1bb3a12b
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn H) (hconn : H.Connected)
    (hmax : ∀ K : SimpleGraph V, HasPlanarDrawingOn K →
      (∀ u v, H.Adj u v → K.Adj u v) →
      K.edgeSet.ncard ≤ H.edgeSet.ncard)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
