-- Prove2me | Theorems.Thm_edge_insert_count_changes_unreachable_components__p2m_e8ef01cf_2886_4f4c_9b6c_0eaa2b16bf24_a2
-- name    : edge_insert_count_changes_unreachable_components__p2m_e8ef01cf_2886_4f4c_9b6c_0eaa2b16bf24_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:32:40.3722+00:00
-- url     : https://prove2.me/theorems/632e18d6-a4cc-4ac2-ab65-0a7319845dde
-- title:
--   Insertion between components merges exactly two
-- statement:
--   This isolates the unreachable-endpoints component case. Unreachability ensures the original components of `u` and `v` are distinct. A proof route is to characterize reachability after insertion: the old component classes remain distinct except that these two classes become one. Counting the resulting finite quotient classes gives a decrease of exactly one. The parent supplies `hne`; no positivity or additional graph hypothesis is needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

theorem edge_insert_count_changes_unreachable_components__p2m_e8ef01cf_2886_4f4c_9b6c_0eaa2b16bf24_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (u v : V) (hne : u ≠ v) (hnreach : ¬ K.Reachable u v) :
    Nat.card K.ConnectedComponent =
      Nat.card (K ⊔ SimpleGraph.edge u v).ConnectedComponent + 1 := by sorry
