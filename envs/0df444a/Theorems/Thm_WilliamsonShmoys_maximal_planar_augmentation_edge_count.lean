-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_augmentation_edge_count
-- name    : WilliamsonShmoys.maximal_planar_augmentation_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:21:10.210222+00:00
-- url     : https://prove2.me/theorems/5f6ac3b6-32b1-4009-9f06-caa1b6fb9eec
-- title:
--   Augmenting a drawable graph to a maximal planar graph
-- statement:
--   For a finite linearly ordered vertex type with at least three vertices, every graph with a crossing-free drawing can be extended, on the same vertex set, to a drawable graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_augmentation_edge_count {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
