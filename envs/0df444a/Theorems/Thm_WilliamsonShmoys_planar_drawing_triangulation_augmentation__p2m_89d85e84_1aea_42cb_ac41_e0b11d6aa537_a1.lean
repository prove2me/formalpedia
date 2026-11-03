-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_augmentation__p2m_89d85e84_1aea_42cb_ac41_e0b11d6aa537_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_augmentation__p2m_89d85e84_1aea_42cb_ac41_e0b11d6aa537_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:59:14.477702+00:00
-- url     : https://prove2.me/theorems/8d9b924c-10a8-4e46-9c92-7f3339daf0a6
-- title:
--   Planar drawing augmentation to an exact triangulation
-- statement:
--   Every drawable finite simple graph on at least three vertices extends on the same vertex set to a drawable graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_augmentation__p2m_89d85e84_1aea_42cb_ac41_e0b11d6aa537_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       3 * Fintype.card V = N.edgeFinset.card + 6) := by sorry
