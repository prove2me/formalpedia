-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_augmentation
-- name    : WilliamsonShmoys.planar_maximal_edge_augmentation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:38:13.948171+00:00
-- url     : https://prove2.me/theorems/ac30454c-036c-4d60-8488-db3ca1396bb2
-- title:
--   Triangulated planar augmentation on a fixed vertex set
-- statement:
--   Every simply drawn planar graph on a finite linearly ordered vertex type with at least three vertices has a planar supergraph on the same vertex set with exactly 3|V|−6 edges. This is proved by augmenting the drawing to a triangulation and applying Euler’s formula; the parent uses maximality to identify the augmentation with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_edge_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
