-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_can_be_completed_to_triangulation
-- name    : WilliamsonShmoys.planar_graph_can_be_completed_to_triangulation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:34:32.91311+00:00
-- url     : https://prove2.me/theorems/fdef6b62-0f54-41ec-8232-9223245cd384
-- title:
--   A finite planar graph can be completed to the maximal planar edge count
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has a crossing-free planar supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_can_be_completed_to_triangulation
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ J : SimpleGraph V,
      H.edgeSet ⊆ J.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      J.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
