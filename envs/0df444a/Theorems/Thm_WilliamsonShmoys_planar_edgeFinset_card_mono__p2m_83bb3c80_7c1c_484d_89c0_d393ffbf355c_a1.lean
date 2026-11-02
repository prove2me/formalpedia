-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edgeFinset_card_mono__p2m_83bb3c80_7c1c_484d_89c0_d393ffbf355c_a1
-- name    : WilliamsonShmoys.planar_edgeFinset_card_mono__p2m_83bb3c80_7c1c_484d_89c0_d393ffbf355c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:05:29.841814+00:00
-- url     : https://prove2.me/theorems/8b62642c-1695-48f9-8df8-b1f402b0c3e5
-- title:
--   Monotonicity of edge count under inclusion
-- statement:
--   If every edge of one finite simple graph is also an edge of another on the same vertices, the first graph’s edge count is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edgeFinset_card_mono__p2m_83bb3c80_7c1c_484d_89c0_d393ffbf355c_a1
    {V : Type} [Fintype V]
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hHK : ∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) :
    H.edgeFinset.card ≤ K.edgeFinset.card := by sorry
