-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_279755a6_02cd_4483_9b65_417cbe6cd492
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_edge_count_279755a6_02cd_4483_9b65_417cbe6cd492
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T17:01:12.746873+00:00
-- url     : https://prove2.me/theorems/707fd91e-f440-4303-9c7c-836f878220fa
-- title:
--   Maximal drawable graphs have the triangulation edge count
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. This removes the embedding and counting work from the parent. The independent route is to interpret the supplied injective continuous arcs as a plane embedding, use maximality to show the graph is connected and every face is triangular, and then apply Euler’s formula and count each edge twice among face boundaries. The lower bound handles the small cases: for three vertices maximality forces the triangle. Formalizing those topological steps for the exact arc predicate is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawingOn_edge_count_279755a6_02cd_4483_9b65_417cbe6cd492
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V,
      K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
