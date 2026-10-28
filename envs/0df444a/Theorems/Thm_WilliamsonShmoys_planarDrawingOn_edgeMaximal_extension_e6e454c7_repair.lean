-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_edgeMaximal_extension_e6e454c7_repair
-- name    : WilliamsonShmoys.planarDrawingOn_edgeMaximal_extension_e6e454c7_repair
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T08:01:43.487567+00:00
-- url     : https://prove2.me/theorems/deba450f-aefa-4a28-908d-48b79e5db839
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable finite simple graph has a drawable edge-maximal supergraph on the same vertex set. This removes the maximal-extension step from the parent. Prove it by choosing a drawable supergraph containing the original graph with the largest edge count among the finitely many simple graphs on the vertex type. The argument also applies when the vertex set has fewer than three elements, and preserves isolated vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_edgeMaximal_extension_e6e454c7_repair
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      N.edgeSet ⊆ P.edgeSet ∧
      ∀ Q : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn Q →
        P.edgeSet ⊆ Q.edgeSet → Q.edgeSet = P.edgeSet := by sorry
