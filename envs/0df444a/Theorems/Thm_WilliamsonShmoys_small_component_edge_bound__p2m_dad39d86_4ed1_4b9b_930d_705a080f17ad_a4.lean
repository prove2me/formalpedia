-- Prove2me | Theorems.Thm_WilliamsonShmoys_small_component_edge_bound__p2m_dad39d86_4ed1_4b9b_930d_705a080f17ad_a4
-- name    : WilliamsonShmoys.small_component_edge_bound__p2m_dad39d86_4ed1_4b9b_930d_705a080f17ad_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:09:45.382003+00:00
-- url     : https://prove2.me/theorems/325daf15-82ea-45e2-a970-94802e98a7da
-- title:
--   Edge bound for a component with fewer than three vertices
-- statement:
--   A simple connected component with fewer than three vertices has at most one edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.small_component_edge_bound__p2m_dad39d86_4ed1_4b9b_930d_705a080f17ad_a4
    {V : Type} [Fintype V]
    (L : SimpleGraph V)
    (C : L.ConnectedComponent)
    (hsmall : C.supp.ncard < 3) :
    C.toSimpleGraph.edgeSet.ncard ≤ 1 := by sorry
