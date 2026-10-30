-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_completion__p2m_2911e589_9855_41f2_81aa_874f2d2a0dd0_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_completion__p2m_2911e589_9855_41f2_81aa_874f2d2a0dd0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:39:29.213853+00:00
-- url     : https://prove2.me/theorems/9bb7986e-be4e-4e64-8783-5fde927124a1
-- title:
--   Connect a planar drawing while preserving its edge bound
-- statement:
--   Every finite drawable simple graph on at least three vertices has a connected drawable supergraph on the same vertices whose edge count is at least as large. Add edges through the complement to join components. This handles disconnected inputs; it does not establish the connected planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_completion__p2m_2911e589_9855_41f2_81aa_874f2d2a0dd0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Connected ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
