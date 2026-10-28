-- Prove2me | Theorems.Thm_WilliamsonShmoys_small_component_induced_edge_bound
-- name    : WilliamsonShmoys.small_component_induced_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:44:03.270971+00:00
-- url     : https://prove2.me/theorems/a769c0e9-7dac-4a54-81e2-808d17db1af4
-- title:
--   Small component edge count is at most its support size
-- statement:
--   A simple graph induced on a connected-component support of fewer than three vertices has at most as many edges as vertices. The support is nonempty; the singleton case has no loops, and the two-vertex case has at most one edge. Prove this by classifying the support cardinality and using looplessness and adjacency symmetry. This supplies the parent’s small-component slack bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.small_component_induced_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (C : K.ConnectedComponent)
    (hC : C.supp.ncard < 3) :
    (K.induce C.supp).edgeSet.ncard ≤ C.supp.ncard := by sorry
