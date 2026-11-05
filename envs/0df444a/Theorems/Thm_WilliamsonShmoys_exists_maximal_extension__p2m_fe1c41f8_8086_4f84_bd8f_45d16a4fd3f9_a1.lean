-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_extension__p2m_fe1c41f8_8086_4f84_bd8f_45d16a4fd3f9_a1
-- name    : WilliamsonShmoys.exists_maximal_extension__p2m_fe1c41f8_8086_4f84_bd8f_45d16a4fd3f9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:44:48.516889+00:00
-- url     : https://prove2.me/theorems/6e3e62cc-a383-40e2-9f18-186252bf1fd3
-- title:
--   A maximal extension for a property on finite graphs
-- statement:
--   For any property of simple graphs on a finite linearly ordered vertex type, if G has the property, then G has a supergraph that is maximal under inclusion among supergraphs with the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_extension__p2m_fe1c41f8_8086_4f84_bd8f_45d16a4fd3f9_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P G) : ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧ ∀ Y : SimpleGraph V, H ≤ Y → P Y → Y ≤ H := by sorry
