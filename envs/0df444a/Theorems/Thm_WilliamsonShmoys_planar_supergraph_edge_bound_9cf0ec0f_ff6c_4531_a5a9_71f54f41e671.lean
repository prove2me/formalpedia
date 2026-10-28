-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_bound_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671
-- name    : WilliamsonShmoys.planar_supergraph_edge_bound_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T03:02:03.36302+00:00
-- url     : https://prove2.me/theorems/52feb103-0724-489f-8f24-3a8db02f8162
-- title:
--   Drawable supergraph with the planar edge lower bound
-- statement:
--   Any drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with at least 3|V|−6 edges. At |V| = 3 the bound is 3, and the conclusion allows a triangle completion. Prove this by extending a planar drawing to a maximal planar supergraph, showing maximality forces triangular faces, and applying Euler’s formula and face-edge incidence counting. This child contains the main topological and counting work removed from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_edge_bound_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * (Fintype.card V : Int) - 6 ≤ (L.edgeSet.ncard : Int) := by sorry
