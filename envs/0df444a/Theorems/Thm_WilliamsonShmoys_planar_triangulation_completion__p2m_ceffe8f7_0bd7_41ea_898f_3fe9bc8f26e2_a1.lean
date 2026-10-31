-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_ceffe8f7_0bd7_41ea_898f_3fe9bc8f26e2_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_ceffe8f7_0bd7_41ea_898f_3fe9bc8f26e2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T09:06:51.136197+00:00
-- url     : https://prove2.me/theorems/65d0e573-2904-4a2f-b00a-11fd7ff50563
-- title:
--   Drawable planar completion with exact edge count
-- statement:
--   A drawable connected finite simple graph with at least three vertices has a drawable supergraph on the same vertex type whose edge count is exactly three times the vertex count minus six. The completion preserves every original edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_ceffe8f7_0bd7_41ea_898f_3fe9bc8f26e2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hConn : P.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
