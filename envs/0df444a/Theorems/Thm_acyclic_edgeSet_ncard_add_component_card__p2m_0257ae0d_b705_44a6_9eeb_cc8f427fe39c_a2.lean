-- Prove2me | Theorems.Thm_acyclic_edgeSet_ncard_add_component_card__p2m_0257ae0d_b705_44a6_9eeb_cc8f427fe39c_a2
-- name    : acyclic_edgeSet_ncard_add_component_card__p2m_0257ae0d_b705_44a6_9eeb_cc8f427fe39c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:10:32.425478+00:00
-- url     : https://prove2.me/theorems/cd99b0ce-6168-4c6b-a6a6-0ae22062f109
-- title:
--   Edge count formula for a finite forest
-- statement:
--   For any finite acyclic simple graph, the number of edges plus the number of connected components equals the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

open SimpleGraph

theorem acyclic_edgeSet_ncard_add_component_card__p2m_0257ae0d_b705_44a6_9eeb_cc8f427fe39c_a2
    {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic) :
    G.edgeSet.ncard + Nat.card G.ConnectedComponent = Fintype.card V := by sorry
