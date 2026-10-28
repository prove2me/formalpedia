-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_graph_has_strict_planar_growth
-- name    : WilliamsonShmoys.planar_drawing_disconnected_graph_has_strict_planar_growth
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:15:36.139619+00:00
-- url     : https://prove2.me/theorems/3f511b85-c912-45f3-a8e4-d03a9f62236e
-- title:
--   A disconnected planar drawing admits strict planar growth
-- statement:
--   For a graph on at least two vertices with the packaged crossing-free drawing, if it is disconnected, add an edge between distinct components along a curve in the complement of the drawing. This preserves planarity and strictly increases the edge count. The vertex lower bound handles the empty-type boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_disconnected_graph_has_strict_planar_growth
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 2 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ G' : SimpleGraph V, G ≤ G' ∧
      WilliamsonShmoys.HasPlanarDrawingOn G' ∧
      G.edgeSet.ncard < G'.edgeSet.ncard := by sorry
