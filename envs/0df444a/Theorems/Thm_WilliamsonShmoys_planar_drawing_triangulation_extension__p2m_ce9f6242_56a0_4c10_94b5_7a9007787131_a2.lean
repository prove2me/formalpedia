-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_ce9f6242_56a0_4c10_94b5_7a9007787131_a2
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_ce9f6242_56a0_4c10_94b5_7a9007787131_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:19:16.015665+00:00
-- url     : https://prove2.me/theorems/e52f58d6-33ee-4b8e-a7a8-0fe00cf44d7c
-- title:
--   Triangulation extension for a connected planar drawing
-- statement:
--   Every connected finite simply drawable graph with at least three vertices is contained in a connected simply drawable graph on the same vertices with exactly 3|V|−6 edges, and its edge count is no larger. The extension carries a decidable adjacency relation so its finite edge count is available in Lean.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_ce9f6242_56a0_4c10_94b5_7a9007787131_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      (letI : DecidableRel H.Adj := dH
       K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
       H.edgeFinset.card = 3 * Fintype.card V - 6 ∧
       K.edgeFinset.card ≤ H.edgeFinset.card) := by sorry
