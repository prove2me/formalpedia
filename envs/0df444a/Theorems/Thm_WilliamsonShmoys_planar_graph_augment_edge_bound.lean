-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_augment_edge_bound
-- name    : WilliamsonShmoys.planar_graph_augment_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T02:42:33.500477+00:00
-- url     : https://prove2.me/theorems/353e1ce9-e61d-47ac-85ac-c60d170e9b1e
-- title:
--   Planar augmentation gives the maximal planar edge bound
-- statement:
--   A graph with a crossing-free drawing on at least three vertices has a planar supergraph on the same vertex set whose edge count is at least 3|V| − 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_augment_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V) :
    Exists fun N : SimpleGraph V =>
      M <= N /\ HasPlanarDrawingOn N /\
      3 * Fintype.card V <= N.edgeSet.ncard + 6 := by sorry
