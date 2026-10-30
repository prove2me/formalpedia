-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_edge_maximal_planar_graph_on
-- name    : WilliamsonShmoys.edge_count_of_edge_maximal_planar_graph_on
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:36:28.987736+00:00
-- url     : https://prove2.me/theorems/bf915881-59f5-4d2f-bd9c-b9a3aabf0457
-- title:
--   Edge count of an edge-maximal planar graph
-- statement:
--   An edge-maximal graph with a crossing-free drawing on at least three vertices has exactly 3n−6 edges. This is the Euler-formula step; a proof must show that edge-maximality forces triangular faces for the supplied drawing notion, including the connectivity and face-boundary cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_edge_maximal_planar_graph_on
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ Q : SimpleGraph V,
      N ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
