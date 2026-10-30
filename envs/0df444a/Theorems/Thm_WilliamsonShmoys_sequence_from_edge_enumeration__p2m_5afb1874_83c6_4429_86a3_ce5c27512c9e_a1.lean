-- Prove2me | Theorems.Thm_WilliamsonShmoys_sequence_from_edge_enumeration__p2m_5afb1874_83c6_4429_86a3_ce5c27512c9e_a1
-- name    : WilliamsonShmoys.sequence_from_edge_enumeration__p2m_5afb1874_83c6_4429_86a3_ce5c27512c9e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:02:14.075947+00:00
-- url     : https://prove2.me/theorems/ecfb6812-4e84-4a6d-b68d-ded72d2e3166
-- title:
--   Build the completion sequence from an edge enumeration
-- statement:
--   Given an enumeration of all edges of H absent from M, build the sequence that adds each listed edge, has disconnected endpoints immediately before each addition, and ends in a connected graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.sequence_from_edge_enumeration__p2m_5afb1874_83c6_4429_86a3_ce5c27512c9e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M H : SimpleGraph V)
    (hMH : M ≤ H)
    (hconn : H.Connected)
    (hbridge : ∀ u v : V, H.Adj u v → ¬ M.Adj u v →
      ¬ (H.deleteEdges {s(u, v)}).Reachable u v)
    {n : Nat} (e : Fin n → V × V)
    (hcanon : ∀ i, (e i).1 < (e i).2)
    (hedge : ∀ i, H.Adj (e i).1 (e i).2 ∧ ¬ M.Adj (e i).1 (e i).2)
    (hdistinct : ∀ i j, i ≠ j → e i ≠ e j)
    (hcover : ∀ u v, H.Adj u v → M.Adj u v ∨
      ∃ i, ((u = (e i).1 ∧ v = (e i).2) ∨ (u = (e i).2 ∧ v = (e i).1))) :
    ∃ (f : Fin (n + 1) → SimpleGraph V),
      f 0 = M ∧
      (∀ x y : V, (f (Fin.last n)).Reachable x y) ∧
      (∀ i : Fin n, ∃ x y : V,
        ¬ (f i.castSucc).Reachable x y ∧
        ∀ u v : V,
          (f i.succ).Adj u v ↔
            (f i.castSucc).Adj u v ∨
              ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) := by sorry
