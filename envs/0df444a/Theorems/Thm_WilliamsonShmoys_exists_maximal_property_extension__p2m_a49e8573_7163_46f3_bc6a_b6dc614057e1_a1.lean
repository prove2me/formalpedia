-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_property_extension__p2m_a49e8573_7163_46f3_bc6a_b6dc614057e1_a1
-- name    : WilliamsonShmoys.exists_maximal_property_extension__p2m_a49e8573_7163_46f3_bc6a_b6dc614057e1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:42:26.383028+00:00
-- url     : https://prove2.me/theorems/11dec6b0-7278-4c2b-bc42-a778db9d922e
-- title:
--   Existence of a maximal property-preserving graph extension
-- statement:
--   For a finite vertex type, every graph satisfying P has a P-satisfying supergraph that is maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_property_extension__p2m_a49e8573_7163_46f3_bc6a_b6dc614057e1_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (K : SimpleGraph V)
    (hK : P K) :
    ∃ M : SimpleGraph V, K ≤ M ∧ P M ∧ ∀ G : SimpleGraph V, M ≤ G → P G → G = M := by sorry
