-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_edge_count_maximal
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_edge_count_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:32:14.352296+00:00
-- url     : https://prove2.me/theorems/e33c5428-74e7-4b66-b4ca-fe2a5731ae2e
-- title:
--   Edge count of a maximal drawable supergraph
-- statement:
--   Every finite graph with a crossing-free drawing and at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V| − 6 edges. The hypotheses cover the small boundary case needed for triangulation. Prove this by choosing an edge-maximal drawable supergraph, showing its drawing is connected with triangular faces, and applying Euler’s formula and face-edge incidence counting. This isolates the augmentation and planar counting argument from the parent; formalizing those facts for HasPlanarDrawingOn remains the core work.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_supergraph_edge_count_maximal
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      G.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V = L.edgeSet.ncard + 6 := by sorry
