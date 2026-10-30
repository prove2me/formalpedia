-- Prove2me | Theorems.Thm_edge_insert_count_changes_edge_card__p2m_e8ef01cf_2886_4f4c_9b6c_0eaa2b16bf24_a2
-- name    : edge_insert_count_changes_edge_card__p2m_e8ef01cf_2886_4f4c_9b6c_0eaa2b16bf24_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:32:38.45081+00:00
-- url     : https://prove2.me/theorems/52895ad6-ba92-4a93-9c32-4a24c62aae63
-- title:
--   Adding an absent edge increments the edge count
-- statement:
--   This isolates the edge-set calculation from the ambient graph and component arguments. Distinctness ensures the single-edge graph has a singleton edge set; absence makes that singleton disjoint from `K.edgeSet`. Rewrite the supremum's edge set as a union and apply finite-cardinality union counting. The strict inequality in the parent supplies `hne`, and `hnot` rules out the only overlap.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

theorem edge_insert_count_changes_edge_card__p2m_e8ef01cf_2886_4f4c_9b6c_0eaa2b16bf24_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (u v : V) (hne : u ≠ v) (hnot : ¬ K.Adj u v) :
    K.edgeSet.ncard + 1 = (K ⊔ SimpleGraph.edge u v).edgeSet.ncard := by sorry
