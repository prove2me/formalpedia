-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_for_euler_count_def6ae5e_bde9_4d7e_98ba_cdd8403c7813
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_for_euler_count_def6ae5e_bde9_4d7e_98ba_cdd8403c7813
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T05:34:00.23522+00:00
-- url     : https://prove2.me/theorems/793ec8c1-4dee-4a97-a4d0-6e6327153b1f
-- title:
--   Maximal drawable graphs have the triangulation edge count
-- statement:
--   A drawable graph maximal under drawable supergraphs on the same finite vertex type, with at least three vertices, has 3n−6 edges. At n = 3, maximality gives the triangle; for larger n, the classical route adds noncrossing edges until every face is triangular, then applies Euler’s formula and counts face-edge incidences. This is the remaining topological obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_drawable_edge_count_for_euler_count_def6ae5e_bde9_4d7e_98ba_cdd8403c7813
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
