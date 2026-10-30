-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_graph_in_set__p2m_adb7eae7_2a82_406a_9d69_125f3f83074d_a1
-- name    : WilliamsonShmoys.exists_maximal_graph_in_set__p2m_adb7eae7_2a82_406a_9d69_125f3f83074d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:10:56.291389+00:00
-- url     : https://prove2.me/theorems/9e2d5bec-4ce3-4d73-a16f-5f4f584d4eff
-- title:
--   A nonempty set of finite simple graphs has a maximal member
-- statement:
--   Every nonempty set of simple graphs on a finite vertex type contains a graph with no strictly larger member of that set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_graph_in_set__p2m_adb7eae7_2a82_406a_9d69_125f3f83074d_a1 {V : Type} [Fintype V] (S : Set (SimpleGraph V)) (hne : S.Nonempty) : ∃ K ∈ S, ∀ L ∈ S, K ≤ L → L = K := by sorry
