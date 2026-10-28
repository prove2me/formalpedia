-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T06:56:18.202864+00:00
-- url     : https://prove2.me/theorems/385c28ad-b5ad-4761-be28-bc66b7135c5c
-- title:
--   Maximal planar graphs have the Euler edge lower bound
-- statement:
--   A planar graph on at least three vertices that has no strictly larger planar supergraph on the same vertex set has at least 3|V|−6 edges. The proof route is to derive the standard Euler bound for a maximal planar embedding: maximality forces faces to be triangular, after which Euler’s formula gives the edge count. This child removes the numerical edge bound from the parent; formalizing Euler’s formula and the consequence of maximality for the given drawing predicate remains the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet ⊆ N.edgeSet) :
    3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by sorry
