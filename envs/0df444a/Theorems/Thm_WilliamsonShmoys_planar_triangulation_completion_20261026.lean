-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_20261026
-- name    : WilliamsonShmoys.planar_triangulation_completion_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:57:11.680213+00:00
-- url     : https://prove2.me/theorems/e5a54b57-1518-4bd6-8fec-c57055b789fe
-- title:
--   Triangulated planar completion on the same vertices
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. The size hypothesis includes the three-vertex boundary, whose maximal planar completion is the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
