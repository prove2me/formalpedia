-- Prove2me | Theorems.Thm_component_vertex_partition_sum__p2m_cd99b0ce_6168_4c6b_a6a6_0ae22062f109_a3
-- name    : component_vertex_partition_sum__p2m_cd99b0ce_6168_4c6b_a6a6_0ae22062f109_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:23:33.453209+00:00
-- url     : https://prove2.me/theorems/79f6e9e4-022e-430a-9212-6dd673326716
-- title:
--   Vertex count partitions across components
-- statement:
--   The sum of the vertex counts of all connected components equals the graph’s vertex count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Set.Card

open SimpleGraph

theorem component_vertex_partition_sum__p2m_cd99b0ce_6168_4c6b_a6a6_0ae22062f109_a3 {V : Type} [Fintype V] (G : SimpleGraph V) [Fintype G.ConnectedComponent] : Finset.univ.sum (fun C : G.ConnectedComponent => Nat.card (C : Set V)) = Fintype.card V := by sorry
