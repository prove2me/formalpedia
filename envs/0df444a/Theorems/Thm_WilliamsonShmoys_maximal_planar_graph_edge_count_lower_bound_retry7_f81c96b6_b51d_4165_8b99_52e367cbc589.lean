-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_lower_bound_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_lower_bound_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T22:42:53.836831+00:00
-- url     : https://prove2.me/theorems/ddd22073-d89c-45ed-9a1c-ee4a0e7442c5
-- title:
--   A maximal planar supergraph has the sharp edge-count lower bound
-- statement:
--   A planar graph on a finite linearly ordered vertex type with at least three vertices has at least 3|V|−6 edges if it has no strictly larger planar supergraph on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_lower_bound_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → K ≠ H →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn K) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
