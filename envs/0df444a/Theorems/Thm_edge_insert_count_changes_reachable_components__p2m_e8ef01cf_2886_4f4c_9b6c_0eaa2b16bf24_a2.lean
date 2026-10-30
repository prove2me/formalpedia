-- Prove2me | Theorems.Thm_edge_insert_count_changes_reachable_components__p2m_e8ef01cf_2886_4f4c_9b6c_0eaa2b16bf24_a2
-- name    : edge_insert_count_changes_reachable_components__p2m_e8ef01cf_2886_4f4c_9b6c_0eaa2b16bf24_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:32:39.129639+00:00
-- url     : https://prove2.me/theorems/e38cb66f-8fc6-4d28-a694-959ea791ff95
-- title:
--   Insertion within a component preserves component count
-- statement:
--   This removes the reachable-endpoints component case from the parent. Since `hreach` already connects the endpoints in `K`, adding their edge does not connect any previously separate components. A proof route is to characterize reachability in the supremum and show it is equivalent to old reachability, then use the induced equivalence of connected-component quotients to preserve their finite cardinality. The result also covers an already-present edge; `hne` records the parent’s distinct-endpoint boundary.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

theorem edge_insert_count_changes_reachable_components__p2m_e8ef01cf_2886_4f4c_9b6c_0eaa2b16bf24_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (u v : V) (hne : u ≠ v) (hreach : K.Reachable u v) :
    Nat.card (K ⊔ SimpleGraph.edge u v).ConnectedComponent =
      Nat.card K.ConnectedComponent := by sorry
