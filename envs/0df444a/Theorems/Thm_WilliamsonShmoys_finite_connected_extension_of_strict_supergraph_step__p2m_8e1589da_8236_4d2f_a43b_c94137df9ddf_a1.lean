-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_connected_extension_of_strict_supergraph_step__p2m_8e1589da_8236_4d2f_a43b_c94137df9ddf_a1
-- name    : WilliamsonShmoys.finite_connected_extension_of_strict_supergraph_step__p2m_8e1589da_8236_4d2f_a43b_c94137df9ddf_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:55:25.629963+00:00
-- url     : https://prove2.me/theorems/7b028f0e-9557-4d63-b320-a3debd61f7f1
-- title:
--   Finite maximal extension from strict supergraph steps
-- statement:
--   If a property holds for a graph on a finite ordered vertex type and every disconnected supergraph satisfying the property has a strict supergraph satisfying it, then there is a connected supergraph satisfying the property. Choose a maximal qualifying supergraph among the finitely many graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_connected_extension_of_strict_supergraph_step__p2m_8e1589da_8236_4d2f_a43b_c94137df9ddf_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P G)
    (hstep : ∀ H : SimpleGraph V, G ≤ H → P H → ¬ H.Connected →
      ∃ H' : SimpleGraph V, H < H' ∧ P H') :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ P H := by sorry
