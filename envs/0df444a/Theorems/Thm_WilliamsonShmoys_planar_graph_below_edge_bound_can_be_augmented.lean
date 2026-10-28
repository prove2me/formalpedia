-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_below_edge_bound_can_be_augmented
-- name    : WilliamsonShmoys.planar_graph_below_edge_bound_can_be_augmented
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T06:44:31.807598+00:00
-- url     : https://prove2.me/theorems/e6494b82-c13d-4728-8e3f-6619a8b5c762
-- title:
--   Augmenting a planar graph below the edge bound
-- statement:
--   If a drawable simple graph on at least three vertices has fewer than three times its number of vertices minus six edges, it has a strictly larger drawable simple supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_below_edge_bound_can_be_augmented
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hSmall : L.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧ M ≠ L := by sorry
