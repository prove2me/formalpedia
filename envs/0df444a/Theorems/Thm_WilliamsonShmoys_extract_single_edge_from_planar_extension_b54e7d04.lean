-- Prove2me | Theorems.Thm_WilliamsonShmoys_extract_single_edge_from_planar_extension_b54e7d04
-- name    : WilliamsonShmoys.extract_single_edge_from_planar_extension_b54e7d04
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:41:27.437385+00:00
-- url     : https://prove2.me/theorems/e268ac56-7442-4d6d-aaee-b4728631b066
-- title:
--   Extract a one-edge planar augmentation from a larger planar extension
-- statement:
--   If a graph is contained in a planar graph on the same finite vertex set, and has fewer edges than the latter's `3n - 6` edges, it can be augmented by exactly one edge while preserving planarity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.extract_single_edge_from_planar_extension_b54e7d04
    {V : Type} [Fintype V] [LinearOrder V]
    (G K : SimpleGraph V)
    (hGK : G.edgeSet ⊆ K.edgeSet)
    (hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hsmall : G.edgeSet.ncard < 3 * Fintype.card V - 6)
    (hKcount : K.edgeSet.ncard = 3 * Fintype.card V - 6) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊂ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = G.edgeSet.ncard + 1 := by sorry
