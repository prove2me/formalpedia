-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_augmentation_below_triangulation_bound
-- name    : WilliamsonShmoys.planar_graph_augmentation_below_triangulation_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T09:23:00.402395+00:00
-- url     : https://prove2.me/theorems/a38ff428-1687-49f2-9a6d-f27e8bffe0e0
-- title:
--   Augmentation of a sparse drawable graph
-- statement:
--   If a drawable simple graph on at least three vertices has fewer than 3|V|−6 edges, then it has a strictly larger drawable supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_augmentation_below_triangulation_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hsmall : 3 * Fintype.card V > L.edgeSet.ncard + 6) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M ≠ L := by sorry
