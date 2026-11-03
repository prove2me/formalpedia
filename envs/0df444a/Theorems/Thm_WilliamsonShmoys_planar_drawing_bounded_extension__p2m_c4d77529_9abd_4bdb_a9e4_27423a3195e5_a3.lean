-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_bounded_extension__p2m_c4d77529_9abd_4bdb_a9e4_27423a3195e5_a3
-- name    : WilliamsonShmoys.planar_drawing_bounded_extension__p2m_c4d77529_9abd_4bdb_a9e4_27423a3195e5_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:01:34.342209+00:00
-- url     : https://prove2.me/theorems/0217dacd-29f2-4bf3-8012-06725ffda067
-- title:
--   Drawable supergraph with planar edge bounds
-- statement:
--   Extend a crossing-free drawing on at least three ordered vertices to a crossing-free supergraph on the same vertices whose edge count is at least the original count, at least Fintype.card V - 2, and at most 3 * Fintype.card V - 6. This removes the drawing-extension and planar edge-count work from the parent. A route is maximal drawable-edge augmentation followed by connectedness, Euler’s formula, and face-boundary counting; the remaining core obligation is to formalize that route for the supplied drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_bounded_extension__p2m_c4d77529_9abd_4bdb_a9e4_27423a3195e5_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     ∃ K : SimpleGraph V, H ≤ K ∧
       WilliamsonShmoys.HasPlanarDrawingOn K ∧
       (letI : DecidableRel K.Adj := Classical.decRel K.Adj
        H.edgeFinset.card ≤ K.edgeFinset.card ∧
        Fintype.card V ≤ K.edgeFinset.card + 2 ∧
        K.edgeFinset.card ≤ 3 * Fintype.card V - 6)) := by sorry
