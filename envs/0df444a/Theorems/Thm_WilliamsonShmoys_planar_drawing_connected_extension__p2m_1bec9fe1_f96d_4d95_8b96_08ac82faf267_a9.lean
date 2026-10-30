-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_1bec9fe1_f96d_4d95_8b96_08ac82faf267_a9
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_1bec9fe1_f96d_4d95_8b96_08ac82faf267_a9
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T08:09:08.711638+00:00
-- url     : https://prove2.me/theorems/5b9626d5-69cf-4a0c-aa91-1bfea1462830
-- title:
--   Extend a nonempty planar drawing to a connected graph
-- statement:
--   Given the parent’s at-least-three-vertices hypothesis, extend any supplied planar drawing to a connected supergraph on the same vertex type, without decreasing the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_1bec9fe1_f96d_4d95_8b96_08ac82faf267_a9
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ N.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (M.edgeSet.ncard : Int) ≤ (N.edgeSet.ncard : Int) := by sorry
