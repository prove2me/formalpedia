-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_sparse_graph_has_planar_edge_augmentation
-- name    : WilliamsonShmoys.planar_sparse_graph_has_planar_edge_augmentation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T05:21:58.814008+00:00
-- url     : https://prove2.me/theorems/2e173d6b-7492-45fe-8c60-9d21f23db62c
-- title:
--   Sparse planar graph admits a planar edge augmentation
-- statement:
--   A planar graph on at least three vertices with fewer than 3n − 6 edges has a strict planar supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.planar_sparse_graph_has_planar_edge_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hsparse : L.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M ≠ L := by sorry
