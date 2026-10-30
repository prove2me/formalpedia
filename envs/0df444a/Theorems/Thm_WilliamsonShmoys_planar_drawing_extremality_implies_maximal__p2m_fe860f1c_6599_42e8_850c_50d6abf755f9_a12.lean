-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extremality_implies_maximal__p2m_fe860f1c_6599_42e8_850c_50d6abf755f9_a12
-- name    : WilliamsonShmoys.planar_drawing_extremality_implies_maximal__p2m_fe860f1c_6599_42e8_850c_50d6abf755f9_a12
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:32:54.967158+00:00
-- url     : https://prove2.me/theorems/85dfe40e-bf21-4653-aec5-d5293b86ee0f
-- title:
--   An extremal planar drawing is inclusion maximal
-- statement:
--   A drawable finite simple graph on at least three vertices with exactly 3|V|−6 edges is inclusion-maximal among drawable graphs on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_extremality_implies_maximal__p2m_fe860f1c_6599_42e8_850c_50d6abf755f9_a12
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hcount : H.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    ∀ M : SimpleGraph V, H ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = H := by sorry
