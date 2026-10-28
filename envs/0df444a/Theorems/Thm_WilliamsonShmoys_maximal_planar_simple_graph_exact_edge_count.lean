-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_graph_exact_edge_count
-- name    : WilliamsonShmoys.maximal_planar_simple_graph_exact_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:15:05.701127+00:00
-- url     : https://prove2.me/theorems/f45772a1-be85-4d4e-8b9a-44c2fcb6f20c
-- title:
--   Maximal planar simple graph exact edge count
-- statement:
--   A simply drawn, edge-maximal simple planar graph on at least three vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_simple_graph_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
