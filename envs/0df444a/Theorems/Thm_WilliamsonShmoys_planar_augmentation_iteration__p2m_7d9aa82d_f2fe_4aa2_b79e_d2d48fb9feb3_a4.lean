-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_iteration__p2m_7d9aa82d_f2fe_4aa2_b79e_d2d48fb9feb3_a4
-- name    : WilliamsonShmoys.planar_augmentation_iteration__p2m_7d9aa82d_f2fe_4aa2_b79e_d2d48fb9feb3_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:02:16.796459+00:00
-- url     : https://prove2.me/theorems/460389d4-31bd-4508-b209-05dd70a4382c
-- title:
--   Iterate planar edge attachments to connectivity
-- statement:
--   If every disconnected planar supergraph admits an exact drawing-preserving addition of an edge between unreachable vertices, finitely many such additions yield a connected planar supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_augmentation_iteration__p2m_7d9aa82d_f2fe_4aa2_b79e_d2d48fb9feb3_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hstep : ∀ (H : SimpleGraph V), G ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H → ¬ H.Connected →
      ∃ (u v : V) (huv : u ≠ v),
        ¬ H.Reachable u v ∧
        ∃ K : SimpleGraph V,
          H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
          ∀ a b, K.Adj a b ↔
            H.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u)) :
    ∃ C : SimpleGraph V,
      G ≤ C ∧ C.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn C := by sorry
