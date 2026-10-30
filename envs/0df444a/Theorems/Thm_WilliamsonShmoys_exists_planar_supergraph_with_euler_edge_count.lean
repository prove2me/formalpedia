-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_euler_edge_count
-- name    : WilliamsonShmoys.exists_planar_supergraph_with_euler_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:03:22.072281+00:00
-- url     : https://prove2.me/theorems/3bf4a646-063e-4e1b-b6a1-0782eed3c5dd
-- title:
--   Extend a drawn planar graph to a triangulation
-- statement:
--   Any finite simple graph with at least three vertices and a crossing-free drawing can be extended, on the same vertex set, to a drawn triangulation with exactly 3|V|−6 edges; the original edge set is included in the extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_planar_supergraph_with_euler_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
