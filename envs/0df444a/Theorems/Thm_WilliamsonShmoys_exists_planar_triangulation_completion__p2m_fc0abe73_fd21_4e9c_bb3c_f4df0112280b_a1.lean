-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_completion__p2m_fc0abe73_fd21_4e9c_bb3c_f4df0112280b_a1
-- name    : WilliamsonShmoys.exists_planar_triangulation_completion__p2m_fc0abe73_fd21_4e9c_bb3c_f4df0112280b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:39:16.080568+00:00
-- url     : https://prove2.me/theorems/18dadb11-49a3-466e-95d7-24d3c5d5bdee
-- title:
--   Planar triangulation completion on the same vertex set
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has a planar supergraph on the same vertex set with exactly 3|V|−6 edges. The vertex bound is retained so the triangulation and edge formula include the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_triangulation_completion__p2m_fc0abe73_fd21_4e9c_bb3c_f4df0112280b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
        K.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
