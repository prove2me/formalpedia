-- Prove2me | Theorems.Thm_component_edge_partition_count__p2m_18b4f874_2377_4148_8ba5_149b9ea6fe45_a1
-- name    : component_edge_partition_count__p2m_18b4f874_2377_4148_8ba5_149b9ea6fe45_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:26:21.474995+00:00
-- url     : https://prove2.me/theorems/ad62d6f2-3818-4a29-8c23-e55e80cb22b1
-- title:
--   Component edge sets partition the graph edge set
-- statement:
--   The number of edges of a finite simple graph equals the sum, over its connected components, of the edge counts in the induced component graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Set.Card

open SimpleGraph

theorem component_edge_partition_count__p2m_18b4f874_2377_4148_8ba5_149b9ea6fe45_a1 {V : Type} [Fintype V] (G : SimpleGraph V) [Fintype G.ConnectedComponent] : G.edgeSet.ncard = Finset.univ.sum (fun C : G.ConnectedComponent => C.toSimpleGraph.edgeSet.ncard) := by sorry
