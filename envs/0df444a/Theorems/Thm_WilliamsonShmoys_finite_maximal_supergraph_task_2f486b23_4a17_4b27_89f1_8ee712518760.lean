-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph_task_2f486b23_4a17_4b27_89f1_8ee712518760
-- name    : WilliamsonShmoys.finite_maximal_supergraph_task_2f486b23_4a17_4b27_89f1_8ee712518760
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:01:34.547654+00:00
-- url     : https://prove2.me/theorems/0fad591c-951c-4aaf-bf33-d2007ab00b50
-- title:
--   Finite maximal supergraph for a graph property
-- statement:
--   For a finite vertex type, every graph satisfying a property has a supergraph that is maximal among graphs satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_maximal_supergraph_task_2f486b23_4a17_4b27_89f1_8ee712518760
    {V : Type} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      P L ∧
      (∀ M : SimpleGraph V, L ≤ M → P M → M = L) := by sorry
