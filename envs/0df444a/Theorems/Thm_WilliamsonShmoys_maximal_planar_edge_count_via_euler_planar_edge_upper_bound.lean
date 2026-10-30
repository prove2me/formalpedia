-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_via_euler_planar_edge_upper_bound
-- name    : WilliamsonShmoys.maximal_planar_edge_count_via_euler_planar_edge_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T20:52:35.334442+00:00
-- url     : https://prove2.me/theorems/f8a5c158-ff19-421c-a609-8d81593076c2
-- title:
--   Euler edge bound for the supplied planar drawing predicate
-- statement:
--   Any graph on at least three vertices with the supplied crossing-free drawing has at most 3|V|−6 edges. A proof route is to establish the plane graph Euler bound for each connected component and account for isolated vertices and disconnected components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_via_euler_planar_edge_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hSdraw : WilliamsonShmoys.HasPlanarDrawingOn S) :
    S.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
