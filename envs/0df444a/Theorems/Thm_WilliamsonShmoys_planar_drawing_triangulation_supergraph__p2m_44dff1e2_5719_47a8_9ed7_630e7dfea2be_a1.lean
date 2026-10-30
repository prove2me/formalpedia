-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph__p2m_44dff1e2_5719_47a8_9ed7_630e7dfea2be_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_supergraph__p2m_44dff1e2_5719_47a8_9ed7_630e7dfea2be_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:52:02.454906+00:00
-- url     : https://prove2.me/theorems/b4255e2c-f98e-48f5-8b5b-17ec5805d9ae
-- title:
--   Planar drawing extends to a triangulated supergraph
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices extends, on the same vertex set, to a crossing-free graph with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_supergraph__p2m_44dff1e2_5719_47a8_9ed7_630e7dfea2be_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V) :
    ∃ T : SimpleGraph V, M ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      T.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
