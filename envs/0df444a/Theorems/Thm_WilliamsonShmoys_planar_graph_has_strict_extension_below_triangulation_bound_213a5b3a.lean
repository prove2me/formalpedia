-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_strict_extension_below_triangulation_bound_213a5b3a
-- name    : WilliamsonShmoys.planar_graph_has_strict_extension_below_triangulation_bound_213a5b3a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:50:36.532429+00:00
-- url     : https://prove2.me/theorems/614dfe52-4c05-4f8e-bdd4-6de164253ca0
-- title:
--   Planar graph below the triangulation bound has a strict extension
-- statement:
--   If a finite simple graph with at least three vertices has a crossing-free drawing and fewer than 3|V| − 6 edges, there is a strict planar supergraph on the same vertices. Prove this by adding drawable edges inside faces until the embedding is triangulated; the strict inequality rules out completion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_strict_extension_below_triangulation_bound_213a5b3a
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hE : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ J : SimpleGraph V, G ≤ J ∧ J ≠ G ∧
      WilliamsonShmoys.HasPlanarDrawingOn J := by sorry
