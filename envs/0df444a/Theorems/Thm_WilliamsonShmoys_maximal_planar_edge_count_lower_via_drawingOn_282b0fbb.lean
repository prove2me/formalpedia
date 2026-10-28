-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_via_drawingOn_282b0fbb
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_via_drawingOn_282b0fbb
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T09:51:10.981608+00:00
-- url     : https://prove2.me/theorems/fac06854-16b9-4ded-ae93-1656e3ccea30
-- title:
--   Edge count lower bound for a maximal graph with a planar drawing
-- statement:
--   A graph maximal under planar edge additions, with a drawing witnessed by HasPlanarDrawingOn and at least three vertices, has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_via_drawingOn_282b0fbb
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → M ≤ L) :
    3 * (Fintype.card V : Int) - 6 <= (L.edgeSet.ncard : Int) := by sorry
