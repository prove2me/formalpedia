-- Prove2me | Theorems.Thm_WilliamsonShmoys_finiteGraph_maximal_extension__p2m_131fddda_53be_4336_ab67_f2e30cf87311_a1
-- name    : WilliamsonShmoys.finiteGraph_maximal_extension__p2m_131fddda_53be_4336_ab67_f2e30cf87311_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:50:33.659312+00:00
-- url     : https://prove2.me/theorems/659d9164-2fe0-4f66-80d7-4792fa5e182d
-- title:
--   Maximal extension in a finite graph order
-- statement:
--   For any predicate on simple graphs over a finite vertex type, every graph satisfying it has a supergraph satisfying it that is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finiteGraph_maximal_extension__p2m_131fddda_53be_4336_ab67_f2e30cf87311_a1 {V : Type} [Fintype V] (L : SimpleGraph V) (P : SimpleGraph V → Prop) (hL : P L) : ∃ M : SimpleGraph V, LE.le L M ∧ P M ∧ ∀ N : SimpleGraph V, LE.le M N → P N → N = M := by sorry
