-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_cbce8d52_767a_43cf_a345_07ed3485307d
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_cbce8d52_767a_43cf_a345_07ed3485307d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:30:27.678165+00:00
-- url     : https://prove2.me/theorems/5b0bedae-c5e2-4d91-a3a8-47d9fbcf03b4
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal simple graph with a planar drawing and at least three vertices has exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_cbce8d52_767a_43cf_a345_07ed3485307d
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ H' : SimpleGraph V,
      H ≤ H' → WilliamsonShmoys.HasPlanarDrawingOn H' → H' = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
