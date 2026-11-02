-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulated_extension__p2m_055aa8e4_db8a_47ed_b733_513d02bcef62_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_triangulated_extension__p2m_055aa8e4_db8a_47ed_b733_513d02bcef62_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:32:03.541725+00:00
-- url     : https://prove2.me/theorems/3a1649bb-b908-4400-8c80-435b14739a2c
-- title:
--   Extension of a drawable graph to a triangulated planar graph
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type of size at least three is a subgraph of a drawable graph on the same vertices with exactly 3|V|−6 edges. This includes disconnected graphs and the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_has_triangulated_extension__p2m_055aa8e4_db8a_47ed_b733_513d02bcef62_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      H.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
