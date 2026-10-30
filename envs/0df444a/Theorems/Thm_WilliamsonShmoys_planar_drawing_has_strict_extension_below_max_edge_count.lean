-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_strict_extension_below_max_edge_count
-- name    : WilliamsonShmoys.planar_drawing_has_strict_extension_below_max_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:20:21.584788+00:00
-- url     : https://prove2.me/theorems/9f4db670-1052-4aa4-ac14-eefb1dacf28a
-- title:
--   Augmenting a subextremal drawable graph
-- statement:
--   If a drawable simple graph on at least three finite ordered vertices has fewer than 3|V|−6 edges, there is a drawable graph on the same vertices whose edge set strictly contains its edge set. The strict numerical hypothesis is essential; at the extremal count a triangulation need not admit any further edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_strict_extension_below_max_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V)
    (hEdges : (G.edgeSet.ncard : Int) < 3 * (Fintype.card V : Int) - 6) :
    ∃ L : SimpleGraph V,
      G.edgeSet ⊂ L.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
