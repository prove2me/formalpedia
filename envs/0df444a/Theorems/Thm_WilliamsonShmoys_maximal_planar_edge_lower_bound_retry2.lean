-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_retry2
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_retry2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:45:45.4183+00:00
-- url     : https://prove2.me/theorems/37d87729-5690-4e86-b2b2-ebb299309a24
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   A finite simple graph with a crossing-free drawing, at least three vertices, and no proper planar supergraph on the same vertex type has at least 3|V|−6 edges. This removes the lower-bound half of the target; maximize the edge count among planar supergraphs, apply maximality, then prove a maximal simple planar graph has triangular faces and use Euler’s formula. The n=3 case is included in the face-count conclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_retry2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V, M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) :
    3 * (Fintype.card V : Int) - 6 <= (M.edgeSet.ncard : Int) := by sorry
