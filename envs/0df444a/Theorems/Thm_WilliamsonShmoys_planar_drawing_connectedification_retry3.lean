-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connectedification_retry3
-- name    : WilliamsonShmoys.planar_drawing_connectedification_retry3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T22:34:04.240508+00:00
-- url     : https://prove2.me/theorems/6c4b5b8d-4314-4d46-bdc8-b242bc55aa0b
-- title:
--   Connectedify a drawable graph with at least three vertices
-- statement:
--   Add noncrossing edges between components to obtain a connected drawable simple graph on the same vertices, without decreasing the edge count. The size hypothesis excludes the empty-vertex counterexample to the earlier version. An independent proof route is to use the finite planar embedding determined by the drawing and connect distinct components through faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connectedification_retry3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
