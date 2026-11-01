-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion__p2m_833458fe_f209_438f_86e7_1012b8725315_a1
-- name    : WilliamsonShmoys.planar_drawing_completion__p2m_833458fe_f209_438f_86e7_1012b8725315_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:47:47.236248+00:00
-- url     : https://prove2.me/theorems/631bc0f5-f3dc-4eb9-811c-fa1521bf437a
-- title:
--   Complete a connected planar drawing to a maximal planar graph
-- statement:
--   Any connected finite simple graph with at least three vertices and a crossing-free drawing can be extended on the same vertices to an inclusion-maximal simple graph with a crossing-free drawing, without decreasing its edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_completion__p2m_833458fe_f209_438f_86e7_1012b8725315_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      H.edgeSet.ncard <= K.edgeSet.ncard ∧
      HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, HasPlanarDrawingOn L →
        (∀ u v, K.Adj u v → L.Adj u v) → L = K) := by sorry
