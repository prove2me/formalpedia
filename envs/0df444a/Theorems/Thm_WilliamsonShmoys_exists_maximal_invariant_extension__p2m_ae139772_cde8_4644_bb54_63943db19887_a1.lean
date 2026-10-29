-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_invariant_extension__p2m_ae139772_cde8_4644_bb54_63943db19887_a1
-- name    : WilliamsonShmoys.exists_maximal_invariant_extension__p2m_ae139772_cde8_4644_bb54_63943db19887_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:51:46.857989+00:00
-- url     : https://prove2.me/theorems/4fd4dfa8-35f1-4d2f-b4df-0c96f8a4da0f
-- title:
--   Finite maximal invariant extension
-- statement:
--   For any graph property P on a finite vertex type, every graph satisfying P has a P-satisfying extension that is maximal among P-satisfying extensions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_invariant_extension__p2m_ae139772_cde8_4644_bb54_63943db19887_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (G : SimpleGraph V) (hG : P G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by sorry
