-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph_for_drawing_edge_bound
-- name    : WilliamsonShmoys.exists_triangulated_planar_supergraph_for_drawing_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:25:38.544673+00:00
-- url     : https://prove2.me/theorems/7ea63d34-d2b6-4051-b748-1d9fbfc9ebbc
-- title:
--   Extend a planar drawing to a triangulated supergraph
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has a triangulated planar supergraph on the same vertices with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_triangulated_planar_supergraph_for_drawing_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hMdraw : HasPlanarDrawingOn M) :
    Exists fun H : SimpleGraph V => M.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
