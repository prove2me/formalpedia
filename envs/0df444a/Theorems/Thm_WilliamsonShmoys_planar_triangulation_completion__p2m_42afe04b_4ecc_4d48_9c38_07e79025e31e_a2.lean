-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_42afe04b_4ecc_4d48_9c38_07e79025e31e_a2
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_42afe04b_4ecc_4d48_9c38_07e79025e31e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:29:05.650327+00:00
-- url     : https://prove2.me/theorems/d3131f9d-f6af-4764-8ee2-8200821979d2
-- title:
--   Triangulation completion of a finite planar drawing
-- statement:
--   Every crossing-free drawing of a finite simple graph on at least three vertices can be extended, by adding edges on the same vertex set, to a crossing-free drawing with exactly 3|V|−6 edges. This is the triangulation-completion step; the parent uses the resulting supergraph’s count and maximality to obtain the target count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_42afe04b_4ecc_4d48_9c38_07e79025e31e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V, K <= H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
