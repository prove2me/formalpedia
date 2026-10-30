-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_component_bounds__p2m_dad39d86_4ed1_4b9b_930d_705a080f17ad_a4
-- name    : WilliamsonShmoys.planar_edge_bound_of_component_bounds__p2m_dad39d86_4ed1_4b9b_930d_705a080f17ad_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:09:47.593184+00:00
-- url     : https://prove2.me/theorems/b5b19615-d8fe-48dd-851e-fbd8937aea78
-- title:
--   Combining edge bounds over connected components
-- statement:
--   If each large connected component satisfies the planar Euler bound and each smaller component has at most one edge, summing component sizes and edge counts proves the global bound for graphs with at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_of_component_bounds__p2m_dad39d86_4ed1_4b9b_930d_705a080f17ad_a4
    {V : Type} [Fintype V]
    (L : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hcomp : ∀ C : L.ConnectedComponent,
      (3 ≤ C.supp.ncard →
        C.toSimpleGraph.edgeSet.ncard + 6 ≤ 3 * C.supp.ncard) ∧
      (C.supp.ncard < 3 → C.toSimpleGraph.edgeSet.ncard ≤ 1)) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
