-- Prove2me | Theorems.Thm_finiteAcyclicSubgraph_edge_count_components__p2m_50f5601b_e154_4acb_9deb_d7586c738d35_a3
-- name    : finiteAcyclicSubgraph_edge_count_components__p2m_50f5601b_e154_4acb_9deb_d7586c738d35_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:05:07.857479+00:00
-- url     : https://prove2.me/theorems/0257ae0d-b705-44a6-9eeb-cc8f427fe39c
-- title:
--   Edge count of an acyclic graph with preserved components
-- statement:
--   For a finite acyclic graph, the number of edges plus the number of connected components of any graph with the same reachability relation equals the number of vertices. Count each acyclic component as a tree and use reachability equivalence to identify component counts.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

theorem finiteAcyclicSubgraph_edge_count_components__p2m_50f5601b_e154_4acb_9deb_d7586c738d35_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (F K : SimpleGraph V) (hF : F.IsAcyclic)
    (hReach : ∀ u v, F.Reachable u v ↔ K.Reachable u v) :
    F.edgeSet.ncard + Nat.card K.ConnectedComponent = Fintype.card V := by sorry
