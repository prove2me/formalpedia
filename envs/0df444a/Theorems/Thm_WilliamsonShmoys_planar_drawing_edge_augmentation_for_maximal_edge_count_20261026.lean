-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_augmentation_for_maximal_edge_count_20261026
-- name    : WilliamsonShmoys.planar_drawing_edge_augmentation_for_maximal_edge_count_20261026
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T02:50:12.591456+00:00
-- url     : https://prove2.me/theorems/818be957-e7c4-4eb2-84ce-f98ac89fa6a9
-- title:
--   Augmenting a sparse planar drawing
-- statement:
--   If a drawable simple graph on at least three vertices has fewer than `3|V| - 6` edges, then it has a strictly larger drawable simple supergraph on the same vertex type. The parent applies maximality to this extension. A proof route is to work with the drawing's faces and insert a missing edge whose arc stays within a face, including the case of disconnected graphs. The strict edge-count hypothesis and vertex lower bound retain the equality and small-size boundaries. The remaining core is formalizing this insertion for the given continuous-arc drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_augmentation_for_maximal_edge_count_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hsmall : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ P : SimpleGraph V, G ≤ P ∧ P ≠ G ∧ WilliamsonShmoys.HasPlanarDrawingOn P := by
  sorry
