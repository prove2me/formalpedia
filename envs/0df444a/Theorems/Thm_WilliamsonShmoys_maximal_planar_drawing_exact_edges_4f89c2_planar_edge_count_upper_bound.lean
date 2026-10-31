-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edges_4f89c2_planar_edge_count_upper_bound
-- name    : WilliamsonShmoys.maximal_planar_drawing_exact_edges_4f89c2_planar_edge_count_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:08:17.714753+00:00
-- url     : https://prove2.me/theorems/1b637744-2a77-4115-87f8-ade18a5d1c1f
-- title:
--   Planar edge count upper bound for the exact edge-count theorem
-- statement:
--   Every graph with the specified crossing-free drawing on at least three vertices has at most 3n − 6 edges. This removes the planar upper-bound argument from the parent. A proof route is to derive the Euler edge inequality for each connected component with at least three vertices, bound smaller components directly, and sum the component bounds. The hypothesis n ≥ 3 ensures the stated global expression is the relevant bound. The remaining core is formalizing the Euler inequality for the exact arc-based drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawing_exact_edges_4f89c2_planar_edge_count_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    R.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
