-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_supergraph_edge_count_bound
-- name    : WilliamsonShmoys.planar_drawing_has_triangulated_supergraph_edge_count_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T00:41:46.626213+00:00
-- url     : https://prove2.me/theorems/2eec570b-ffd5-435e-a8fa-d87718384d1c
-- title:
--   Triangulated planar supergraph with maximal edge count
-- statement:
--   Extend any finite simple graph with a crossing-free drawing and at least three vertices to a planar supergraph on the same vertices whose edge count is exactly three times the vertex count minus six. The parent uses inclusion to compare edge counts and then finishes arithmetically.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_triangulated_supergraph_edge_count_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
