-- Prove2me | Theorems.Thm_finite_edge_insertion_closure__p2m_32fb842e_c5cc_4fb3_a16d_c8f1f928ca75_a2
-- name    : finite_edge_insertion_closure__p2m_32fb842e_c5cc_4fb3_a16d_c8f1f928ca75_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:21:16.259881+00:00
-- url     : https://prove2.me/theorems/313288c9-76e4-493b-841a-755972300fa5
-- title:
--   Closure under finite edge insertion
-- statement:
--   Any property true of the empty graph and preserved by every legal single-edge insertion into a partial subgraph of `G` holds for every subgraph of `G`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

theorem finite_edge_insertion_closure__p2m_32fb842e_c5cc_4fb3_a16d_c8f1f928ca75_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (Q : SimpleGraph V → Prop)
    (hbase : Q ⊥)
    (hstep : ∀ (K : SimpleGraph V), K ≤ G →
      ∀ u v : V, u < v → G.Adj u v → ¬ K.Adj u v →
      Q K → Q (K ⊔ SimpleGraph.edge u v)) :
    ∀ H : SimpleGraph V, H ≤ G → Q H := by sorry
