-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_extension_ascent
-- name    : WilliamsonShmoys.finite_graph_extension_ascent
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T17:59:44.093869+00:00
-- url     : https://prove2.me/theorems/4993c49e-ed75-4383-8818-120ae593a84c
-- title:
--   Finite ascent reaches a connected graph
-- statement:
--   For any predicate on graphs over a finite vertex type, if the initial graph satisfies the predicate and every disconnected satisfying extension admits a strictly larger satisfying extension, then there is a connected satisfying extension with at least as many edges as the initial graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_graph_extension_ascent {V : Type} [Fintype V] (K : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P K) (hstep : ∀ (L : SimpleGraph V), K ≤ L → P L → ¬ L.Connected → ∃ M : SimpleGraph V, L ≤ M ∧ P M ∧ L.edgeSet.ncard < M.edgeSet.ncard) : ∃ L : SimpleGraph V, K ≤ L ∧ L.Connected ∧ P L ∧ K.edgeSet.ncard ≤ L.edgeSet.ncard := by sorry
