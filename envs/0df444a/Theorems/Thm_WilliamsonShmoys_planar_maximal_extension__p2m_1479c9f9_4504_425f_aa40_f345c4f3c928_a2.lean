-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_1479c9f9_4504_425f_aa40_f345c4f3c928_a2
-- name    : WilliamsonShmoys.planar_maximal_extension__p2m_1479c9f9_4504_425f_aa40_f345c4f3c928_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:56:06.469307+00:00
-- url     : https://prove2.me/theorems/c0b9f0a4-b346-4e7f-8979-6d9d8d607fa9
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_extension__p2m_1479c9f9_4504_425f_aa40_f345c4f3c928_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
