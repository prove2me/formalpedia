-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_finset_induce_b095f50e
-- name    : WilliamsonShmoys.planar_drawing_finset_induce_b095f50e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:43:53.415381+00:00
-- url     : https://prove2.me/theorems/96af8ab5-1056-422e-9d2a-59a051c30a09
-- title:
--   Restrict a planar drawing to a finite induced subgraph
-- statement:
--   The induced subgraph on a finite vertex set inherits the drawing by reusing its positions and arcs. Every induced edge is an original edge, so all continuity, injectivity, endpoint, and nonintersection conditions remain true. Using a `Finset` makes the subtype finite and avoids the instance failure in the previous candidate. A direct proof route is to unpack the drawing witnesses, reuse them, and discharge each condition from induced adjacency.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_finset_induce_b095f50e
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn W)
    (S : Finset V) :
    WilliamsonShmoys.HasPlanarDrawingOn (W.induce (↑S : Set V)) := by sorry
