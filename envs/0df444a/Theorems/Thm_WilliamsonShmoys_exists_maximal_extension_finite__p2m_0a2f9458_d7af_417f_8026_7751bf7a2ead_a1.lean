-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_finite__p2m_0a2f9458_d7af_417f_8026_7751bf7a2ead_a1
-- name    : WilliamsonShmoys.exists_maximal_extension_finite__p2m_0a2f9458_d7af_417f_8026_7751bf7a2ead_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:53:17.142576+00:00
-- url     : https://prove2.me/theorems/69c372b5-3bc5-4c70-875f-df6e04af61b2
-- title:
--   Finite maximal extension for a downward-closed graph property
-- statement:
--   On a finite vertex type, every graph satisfying a downward-closed property has an extension maximal among graphs satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_extension_finite__p2m_0a2f9458_d7af_417f_8026_7751bf7a2ead_a1 {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G) (K : SimpleGraph V) (hK : P K) : ∃ L : SimpleGraph V, K ≤ L ∧ P L ∧ ∀ M : SimpleGraph V, L ≤ M → P M → M ≤ L := by sorry
