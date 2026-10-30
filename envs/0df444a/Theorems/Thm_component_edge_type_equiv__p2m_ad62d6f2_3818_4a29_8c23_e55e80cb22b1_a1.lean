-- Prove2me | Theorems.Thm_component_edge_type_equiv__p2m_ad62d6f2_3818_4a29_8c23_e55e80cb22b1_a1
-- name    : component_edge_type_equiv__p2m_ad62d6f2_3818_4a29_8c23_e55e80cb22b1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:18:03.359787+00:00
-- url     : https://prove2.me/theorems/12205e7e-cfa4-4a2d-8cc9-195547690507
-- title:
--   Edges are partitioned by connected component
-- statement:
--   The edge set of a graph is equivalent to the disjoint union, indexed by connected components, of the edge sets of the induced component graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Set.Card

open SimpleGraph

theorem component_edge_type_equiv__p2m_ad62d6f2_3818_4a29_8c23_e55e80cb22b1_a1 {V : Type} (G : SimpleGraph V) : Nonempty (G.edgeSet ≃ Σ C : G.ConnectedComponent, C.toSimpleGraph.edgeSet) := by sorry
