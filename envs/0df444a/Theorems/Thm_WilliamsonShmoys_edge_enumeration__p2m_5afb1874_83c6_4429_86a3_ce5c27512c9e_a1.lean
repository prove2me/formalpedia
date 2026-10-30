-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_enumeration__p2m_5afb1874_83c6_4429_86a3_ce5c27512c9e_a1
-- name    : WilliamsonShmoys.edge_enumeration__p2m_5afb1874_83c6_4429_86a3_ce5c27512c9e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:02:16.939341+00:00
-- url     : https://prove2.me/theorems/8eaf2b3c-cb44-4211-9f7e-79df5bae9718
-- title:
--   Enumerate the edges absent from the subgraph
-- statement:
--   Every edge of H that is absent from M can be listed once as an ordered pair with its endpoints in strict order, and the list covers exactly the edges needed to extend M to H.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.edge_enumeration__p2m_5afb1874_83c6_4429_86a3_ce5c27512c9e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M H : SimpleGraph V) (hMH : M ≤ H) :
    ∃ (n : Nat) (e : Fin n → V × V),
      (∀ i, (e i).1 < (e i).2) ∧
      (∀ i, H.Adj (e i).1 (e i).2 ∧ ¬ M.Adj (e i).1 (e i).2) ∧
      (∀ i j, i ≠ j → e i ≠ e j) ∧
      (∀ u v, H.Adj u v → M.Adj u v ∨
        ∃ i, ((u = (e i).1 ∧ v = (e i).2) ∨ (u = (e i).2 ∧ v = (e i).1))) := by sorry
