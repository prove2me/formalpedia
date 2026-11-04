-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph__p2m_abe63458_bbbb_493a_8df0_3e0f2c6fa377_a1
-- name    : WilliamsonShmoys.planar_graph_has_triangulated_supergraph__p2m_abe63458_bbbb_493a_8df0_3e0f2c6fa377_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:54:53.896452+00:00
-- url     : https://prove2.me/theorems/b8daf038-e3c0-4a60-b7f6-5a7661d4dadb
-- title:
--   Planar graph completion to a triangulation
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges. The extension is obtained by adding edges until the embedding is triangulated, then counting edges using Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_triangulated_supergraph__p2m_abe63458_bbbb_493a_8df0_3e0f2c6fa377_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       3 * Fintype.card V = K.edgeFinset.card + 6) := by sorry
