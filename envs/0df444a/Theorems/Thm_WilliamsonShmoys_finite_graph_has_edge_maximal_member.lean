-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_has_edge_maximal_member
-- name    : WilliamsonShmoys.finite_graph_has_edge_maximal_member
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T10:16:34.243281+00:00
-- url     : https://prove2.me/theorems/d436c837-c8d7-40b3-98a4-13c7c8155e25
-- title:
--   Finite graph properties have an edge-maximal extension
-- statement:
--   For any property of graphs on a finite vertex type, every graph satisfying that property has an extension satisfying it that is maximal among such extensions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_graph_has_edge_maximal_member {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (K : SimpleGraph V) (hK : P K) : ∃ L : SimpleGraph V, K ≤ L ∧ P L ∧ ∀ M : SimpleGraph V, L ≤ M → P M → M = L := by sorry
