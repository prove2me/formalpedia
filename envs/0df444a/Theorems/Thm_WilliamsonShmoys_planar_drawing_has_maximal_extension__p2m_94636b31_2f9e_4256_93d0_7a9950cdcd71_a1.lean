-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension__p2m_94636b31_2f9e_4256_93d0_7a9950cdcd71_a1
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_94636b31_2f9e_4256_93d0_7a9950cdcd71_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:13:36.256678+00:00
-- url     : https://prove2.me/theorems/21abd8cf-71a5-4301-9a22-948ffb9f2078
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Any drawable graph on a fixed finite ordered vertex set of size at least three has a drawable supergraph on the same vertex set that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_94636b31_2f9e_4256_93d0_7a9950cdcd71_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ (L : SimpleGraph V) [DecidableRel L.Adj],
        HasPlanarDrawingOn L → K ≤ L → L ≤ K := by sorry
