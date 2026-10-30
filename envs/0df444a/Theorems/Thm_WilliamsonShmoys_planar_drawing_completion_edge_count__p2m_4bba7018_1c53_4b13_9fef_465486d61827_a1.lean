-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_edge_count__p2m_4bba7018_1c53_4b13_9fef_465486d61827_a1
-- name    : WilliamsonShmoys.planar_drawing_completion_edge_count__p2m_4bba7018_1c53_4b13_9fef_465486d61827_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:52:24.530244+00:00
-- url     : https://prove2.me/theorems/6a8f39b0-bd46-412b-a379-1f5e129b67f1
-- title:
--   Triangulated planar completion on the same vertex set
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type of size at least three has a planar supergraph on that same vertex type with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_completion_edge_count__p2m_4bba7018_1c53_4b13_9fef_465486d61827_a1
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
