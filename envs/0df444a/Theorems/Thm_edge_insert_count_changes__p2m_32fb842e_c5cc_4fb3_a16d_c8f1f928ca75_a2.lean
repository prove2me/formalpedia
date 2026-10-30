-- Prove2me | Theorems.Thm_edge_insert_count_changes__p2m_32fb842e_c5cc_4fb3_a16d_c8f1f928ca75_a2
-- name    : edge_insert_count_changes__p2m_32fb842e_c5cc_4fb3_a16d_c8f1f928ca75_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:21:17.565756+00:00
-- url     : https://prove2.me/theorems/e8ef01cf-2886-4f4c-9b6c-0eaa2b16bf24
-- title:
--   Edge and component counts under one insertion
-- statement:
--   Adding an absent edge between distinct vertices increments the edge count. It preserves the number of components when the endpoints were already reachable, and otherwise merges exactly two components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

theorem edge_insert_count_changes__p2m_32fb842e_c5cc_4fb3_a16d_c8f1f928ca75_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G K : SimpleGraph V) (hKG : K ≤ G)
    (u v : V) (huv : u < v) (hadj : G.Adj u v) (hnot : ¬ K.Adj u v) :
    K.edgeSet.ncard + 1 = (K ⊔ SimpleGraph.edge u v).edgeSet.ncard ∧
    (∀ hreach : K.Reachable u v,
      Nat.card (K ⊔ SimpleGraph.edge u v).ConnectedComponent =
        Nat.card K.ConnectedComponent) ∧
    (∀ hnreach : ¬ K.Reachable u v,
      Nat.card K.ConnectedComponent =
        Nat.card (K ⊔ SimpleGraph.edge u v).ConnectedComponent + 1) := by sorry
