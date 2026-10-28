-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_connected_supergraph
-- name    : WilliamsonShmoys.planar_drawingOn_connected_supergraph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T12:28:16.314798+00:00
-- url     : https://prove2.me/theorems/b1551092-8e92-4de5-81e3-e07a2208c508
-- title:
--   Connected planar supergraph from a drawing
-- statement:
--   Given a crossing-free drawing of a finite graph with at least three vertices, construct a connected planar supergraph on the same vertex set. The lower bound on the vertex count rules out the empty-vertex obstruction. Prove this by treating the drawing as a finite plane embedding, finding a face incident to distinct graph components via the connected planar dual, and repeatedly adding an arc through such a face until the graph is connected. This isolates the geometric augmentation work; the parent derives the edge-count conclusion from edge-set inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_connected_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hV : 3 <= Fintype.card V) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧ Q.Connected := by sorry
