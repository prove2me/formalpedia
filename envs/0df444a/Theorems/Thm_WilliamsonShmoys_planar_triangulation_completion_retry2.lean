-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_retry2
-- name    : WilliamsonShmoys.planar_triangulation_completion_retry2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:52:59.396887+00:00
-- url     : https://prove2.me/theorems/65589cf5-10f1-4aea-b498-6e2c456062b9
-- title:
--   Drawable supergraph attaining the planar edge bound
-- statement:
--   Every drawable simple graph on the same finite vertex type, with at least three vertices, is a subgraph of a drawable graph with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion_retry2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
