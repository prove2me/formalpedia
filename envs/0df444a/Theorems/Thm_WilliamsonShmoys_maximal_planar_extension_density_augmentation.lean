-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_density_augmentation
-- name    : WilliamsonShmoys.maximal_planar_extension_density_augmentation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:45:22.478475+00:00
-- url     : https://prove2.me/theorems/3edeea81-4678-4d7e-9156-ecaccaea0c7c
-- title:
--   A drawable graph extends to one with the planar edge lower bound
-- statement:
--   For every drawable simple graph on at least three vertices, there is a drawable supergraph on the same vertex set with at least 3|V|−6 edges. Extend the drawing to a maximal planar graph, triangulate its faces, and apply the Euler edge count. The extension must retain all vertices, including isolated vertices; when |V|=3, the triangle supplies the boundary case. This lemma removes the target's maximality condition and leaves the topological augmentation and counting argument as the core proof obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_extension_density_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      L.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by sorry
