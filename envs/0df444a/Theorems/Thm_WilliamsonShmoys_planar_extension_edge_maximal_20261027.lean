-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_edge_maximal_20261027
-- name    : WilliamsonShmoys.planar_extension_edge_maximal_20261027
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:27:13.014534+00:00
-- url     : https://prove2.me/theorems/4075bb7c-6b22-4cdd-980c-e6fbe5929aba
-- title:
--   Finite planar edge-maximal extension
-- statement:
--   Every finite drawable graph has a planar supergraph on the same vertices whose edge count is largest among all planar supergraphs on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_extension_edge_maximal_20261027
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
