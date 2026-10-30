-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_principle__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a1
-- name    : WilliamsonShmoys.planar_extension_principle__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T18:45:32.521459+00:00
-- url     : https://prove2.me/theorems/5852e9a6-6924-436b-b46b-8836657b1500
-- title:
--   Finite maximal planar extension principle
-- statement:
--   If every disconnected planar supergraph of a finite graph has a strict planar supergraph, then the original graph has a connected planar supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_principle__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hstep : ∀ H : SimpleGraph V, G ≤ H → HasPlanarDrawingOn H →
      ¬ H.Connected → ∃ K : SimpleGraph V, H < K ∧ HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
