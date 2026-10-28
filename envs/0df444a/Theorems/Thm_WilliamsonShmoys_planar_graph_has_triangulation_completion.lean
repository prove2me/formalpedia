-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulation_completion
-- name    : WilliamsonShmoys.planar_graph_has_triangulation_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T00:07:30.587407+00:00
-- url     : https://prove2.me/theorems/584c8b76-bd83-4573-8170-cd34643c6778
-- title:
--   Planar graph triangulation completion
-- statement:
--   Any finite simple graph with at least three vertices and a drawing satisfying the supplied planar drawing predicate has a planar supergraph on the same vertices with exactly 3|V|−6 edges. This is the triangulation completion step used by the parent proof.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_triangulation_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
