-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_b713f078_5664_4fa1_8fbb_c01b75fa1e9e_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_b713f078_5664_4fa1_8fbb_c01b75fa1e9e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:31:29.349264+00:00
-- url     : https://prove2.me/theorems/55ddcaf2-84d6-4a74-8795-9ad03c9060dc
-- title:
--   Edge count of an inclusion-maximal planar drawing
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly `3|V| - 6` edges, by planar triangulation and Euler's formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_b713f078_5664_4fa1_8fbb_c01b75fa1e9e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V)
    (hmax : forall K : SimpleGraph V,
      H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
