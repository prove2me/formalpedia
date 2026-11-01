-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_iteration__p2m_7d9aa82d_f2fe_4aa2_b79e_d2d48fb9feb3_a5
-- name    : WilliamsonShmoys.planar_augmentation_iteration__p2m_7d9aa82d_f2fe_4aa2_b79e_d2d48fb9feb3_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:12:36.982247+00:00
-- url     : https://prove2.me/theorems/bfd9de26-18b5-4f80-88aa-03ffeafbf182
-- title:
--   Iterate planar edge attachments to connectivity with a size bound
-- statement:
--   If every disconnected planar supergraph of a finite graph on at least three vertices admits an exact drawing-preserving edge addition between unreachable vertices, finitely many such additions yield a connected planar supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_augmentation_iteration__p2m_7d9aa82d_f2fe_4aa2_b79e_d2d48fb9feb3_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V)
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
