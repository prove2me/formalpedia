-- Prove2me | Theorems.Thm_acyclic_components_tree_edge_formula__p2m_cd99b0ce_6168_4c6b_a6a6_0ae22062f109_a3
-- name    : acyclic_components_tree_edge_formula__p2m_cd99b0ce_6168_4c6b_a6a6_0ae22062f109_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:23:30.345824+00:00
-- url     : https://prove2.me/theorems/a8b58a92-f0b0-4d85-a7e3-8602df87ccf2
-- title:
--   Finite edge formula for an acyclic component
-- statement:
--   The induced graph on each connected component of a finite acyclic graph has one fewer edge than vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Set.Card

open SimpleGraph

theorem acyclic_components_tree_edge_formula__p2m_cd99b0ce_6168_4c6b_a6a6_0ae22062f109_a3 {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic) (C : G.ConnectedComponent) : C.toSimpleGraph.edgeSet.ncard + 1 = Nat.card (C : Set V) := by sorry
