-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_completion__p2m_5bb6036a_c064_4854_9d2e_96dfd53e9e35_a2
-- name    : WilliamsonShmoys.planar_drawing_has_triangulated_completion__p2m_5bb6036a_c064_4854_9d2e_96dfd53e9e35_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:55:40.466027+00:00
-- url     : https://prove2.me/theorems/64f9a932-9abc-4892-8345-6d855cf8c7f4
-- title:
--   Triangulated completion of a planar drawing
-- statement:
--   Any graph on a finite linearly ordered vertex type with at least three vertices that admits the specified crossing-free drawing is contained in a drawable graph on the same vertices with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_triangulated_completion__p2m_5bb6036a_c064_4854_9d2e_96dfd53e9e35_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
       3 * Fintype.card V - 6 = K.edgeFinset.card) := by sorry
