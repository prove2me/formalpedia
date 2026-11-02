-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_induce__p2m_ee19bce3_aed2_4043_9cb4_9bf993438165_a1
-- name    : WilliamsonShmoys.planar_drawingOn_induce__p2m_ee19bce3_aed2_4043_9cb4_9bf993438165_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:07:43.369326+00:00
-- url     : https://prove2.me/theorems/849b1f30-f173-4fb3-b5f0-e65ffe965baf
-- title:
--   Restrict a planar drawing to an induced subgraph
-- statement:
--   Restricting the vertex placement and edge arcs of a drawing to the vertices in a finite subset gives a drawing, in the same sense, of the induced subgraph. This supplies the drawing hypothesis needed when applying the connected bound to each connected induced component.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawingOn_induce__p2m_ee19bce3_aed2_4043_9cb4_9bf993438165_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (s : Finset V) :
    WilliamsonShmoys.HasPlanarDrawingOn (G.induce (↑s : Set V)) := by sorry
