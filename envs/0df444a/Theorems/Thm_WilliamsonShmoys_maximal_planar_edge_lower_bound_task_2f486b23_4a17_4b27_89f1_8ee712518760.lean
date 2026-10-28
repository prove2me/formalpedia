-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_task_2f486b23_4a17_4b27_89f1_8ee712518760
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_task_2f486b23_4a17_4b27_89f1_8ee712518760
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T20:16:27.652787+00:00
-- url     : https://prove2.me/theorems/fa3e2105-66be-4d2e-8adf-a2c14e35ff5c
-- title:
--   Maximal planar edge count lower bound
-- statement:
--   An inclusion-maximal simple graph with a planar drawing and at least three vertices has at least 3|V|−6 edges. The boundary |V| = 3 is included. The proof route is to use maximality to obtain connectedness and triangular faces, then apply Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_task_2f486b23_4a17_4b27_89f1_8ee712518760
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by sorry
