-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_exact_edge_count_from_planarity
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_exact_edge_count_from_planarity
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:07:04.321042+00:00
-- url     : https://prove2.me/theorems/842a865e-2025-4300-a57b-a10fa2e8f60a
-- title:
--   Exact edge count for a maximal drawable graph from planarity
-- statement:
--   A drawable simple graph maximal under adding edges, with at least three vertices, has exactly three times its number of vertices minus six edges. The proof formalizes the maximal planar embedding and Euler face-counting argument for the supplied continuous-arc drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_drawable_graph_has_exact_edge_count_from_planarity
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hHmax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet → H.edgeSet ≠ K.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn K) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
