-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edgeSet_ncard_ge
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_edgeSet_ncard_ge
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:02:15.98269+00:00
-- url     : https://prove2.me/theorems/ec32842e-409d-4410-855b-5f46efdc1635
-- title:
--   Lower bound for a maximal drawable graph
-- statement:
--   A drawable graph maximal among drawable supergraphs on the same vertex type has at least 3|V|−6 edges when there are at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawingOn_edgeSet_ncard_ge
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J) :
    3 * Fintype.card V - 6 ≤ J.edgeSet.ncard := by sorry
