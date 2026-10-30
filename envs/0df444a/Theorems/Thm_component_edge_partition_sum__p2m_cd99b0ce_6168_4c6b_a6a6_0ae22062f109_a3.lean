-- Prove2me | Theorems.Thm_component_edge_partition_sum__p2m_cd99b0ce_6168_4c6b_a6a6_0ae22062f109_a3
-- name    : component_edge_partition_sum__p2m_cd99b0ce_6168_4c6b_a6a6_0ae22062f109_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:23:30.632505+00:00
-- url     : https://prove2.me/theorems/18b4f874-2377-4148-8ba5-149b9ea6fe45
-- title:
--   Edge count partitions across components
-- statement:
--   Summing the induced component edge counts and one per component gives the graph’s edge count plus its number of connected components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Set.Card

open SimpleGraph

theorem component_edge_partition_sum__p2m_cd99b0ce_6168_4c6b_a6a6_0ae22062f109_a3 {V : Type} [Fintype V] (G : SimpleGraph V) [Fintype G.ConnectedComponent] : G.edgeSet.ncard + Nat.card G.ConnectedComponent = Finset.univ.sum (fun C : G.ConnectedComponent => C.toSimpleGraph.edgeSet.ncard + 1) := by sorry
