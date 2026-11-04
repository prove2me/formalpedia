-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_extension__p2m_3bd27e40_28f0_4f6f_8869_04bf87b1e140_a1
-- name    : WilliamsonShmoys.planar_drawing_has_triangulated_extension__p2m_3bd27e40_28f0_4f6f_8869_04bf87b1e140_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:38:43.820862+00:00
-- url     : https://prove2.me/theorems/9ca2ebd3-f99a-4019-8342-a41927f598bc
-- title:
--   Completion of a planar drawing to the maximal planar edge count
-- statement:
--   Every finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_triangulated_extension__p2m_3bd27e40_28f0_4f6f_8869_04bf87b1e140_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := dK
       H.edgeFinset ⊆ K.edgeFinset ∧
       K.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
