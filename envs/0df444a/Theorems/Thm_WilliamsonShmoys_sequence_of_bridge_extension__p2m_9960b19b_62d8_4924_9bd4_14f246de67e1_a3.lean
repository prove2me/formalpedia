-- Prove2me | Theorems.Thm_WilliamsonShmoys_sequence_of_bridge_extension__p2m_9960b19b_62d8_4924_9bd4_14f246de67e1_a3
-- name    : WilliamsonShmoys.sequence_of_bridge_extension__p2m_9960b19b_62d8_4924_9bd4_14f246de67e1_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:58:10.542643+00:00
-- url     : https://prove2.me/theorems/5afb1874-83c6-4429-86a3-ce5c27512c9e
-- title:
--   Enumerate bridge edges to obtain a completion sequence
-- statement:
--   Given a finite connected supergraph of M in which each edge absent from M disconnects its endpoints when deleted, enumerate the added edges to form a sequence that adds each edge once, with unreachable endpoints before each addition and a connected final graph. If there are no added edges, the sequence has length zero.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.sequence_of_bridge_extension__p2m_9960b19b_62d8_4924_9bd4_14f246de67e1_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M H : SimpleGraph V)
    (hMH : M ≤ H)
    (hconn : H.Connected)
    (hbridge : ∀ u v : V, H.Adj u v → ¬ M.Adj u v →
      ¬ (H.deleteEdges {s(u, v)}).Reachable u v) :
    ∃ (n : Nat) (f : Fin (n + 1) → SimpleGraph V),
      f 0 = M ∧
      (∀ x y : V, (f (Fin.last n)).Reachable x y) ∧
      (∀ i : Fin n, ∃ x y : V,
        ¬ (f i.castSucc).Reachable x y ∧
        ∀ u v : V,
          (f i.succ).Adj u v ↔
            (f i.castSucc).Adj u v ∨
              ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) := by sorry
