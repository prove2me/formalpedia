-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_v2
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:37:29.321157+00:00
-- url     : https://prove2.me/theorems/1714170f-d5a6-4069-9c76-3579e6127485
-- title:
--   Triangulated planar completion on the same vertices
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has a crossing-free supergraph on the same vertex set with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_completion_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      W.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
