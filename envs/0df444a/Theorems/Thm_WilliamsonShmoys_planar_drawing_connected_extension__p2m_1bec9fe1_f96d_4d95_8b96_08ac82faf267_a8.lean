-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_1bec9fe1_f96d_4d95_8b96_08ac82faf267_a8
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_1bec9fe1_f96d_4d95_8b96_08ac82faf267_a8
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-29T07:32:59.379259+00:00
-- url     : https://prove2.me/theorems/a7f824b7-7380-4a76-bba3-5118b7001b33
-- title:
--   Extend a planar drawing to a connected graph
-- statement:
--   Every finite graph with the supplied planar drawing has a connected supergraph on the same vertices with a planar drawing, whose edge count is at least the original edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_1bec9fe1_f96d_4d95_8b96_08ac82faf267_a8
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ N.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (M.edgeSet.ncard : Int) ≤ (N.edgeSet.ncard : Int) := by sorry
