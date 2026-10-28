-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_edge_count_93a36477_a46b_4b11_b4cb_7379952edbbc
-- name    : WilliamsonShmoys.planar_supergraph_triangulation_edge_count_93a36477_a46b_4b11_b4cb_7379952edbbc
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T12:28:48.811202+00:00
-- url     : https://prove2.me/theorems/907fef5d-3e60-4833-bd96-3fd976d3ef43
-- title:
--   Drawable supergraph with maximal planar edge count (job-specific declaration)
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_triangulation_edge_count_93a36477_a46b_4b11_b4cb_7379952edbbc
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Exists fun M : SimpleGraph V => L <= M /\ WilliamsonShmoys.HasPlanarDrawingOn M /\
      3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
