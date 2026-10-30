-- Prove2me | Theorems.Thm_empty_graph_component_count__p2m_32fb842e_c5cc_4fb3_a16d_c8f1f928ca75_a2
-- name    : empty_graph_component_count__p2m_32fb842e_c5cc_4fb3_a16d_c8f1f928ca75_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:21:20.861+00:00
-- url     : https://prove2.me/theorems/2ac3fd70-bccf-43e4-bcae-500efefc4d6e
-- title:
--   Connected components of the empty graph
-- statement:
--   The empty graph has one connected component for each vertex, including when the vertex type is empty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

theorem empty_graph_component_count__p2m_32fb842e_c5cc_4fb3_a16d_c8f1f928ca75_a2
    {V : Type} [Fintype V] :
    Nat.card (⊥ : SimpleGraph V).ConnectedComponent = Fintype.card V := by sorry
