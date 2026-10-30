-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_spanning_forest__p2m_1ef7e65a_ff27_4a11_b32b_f50205c0891f_a5
-- name    : WilliamsonShmoys_planar_drawing_spanning_forest__p2m_1ef7e65a_ff27_4a11_b32b_f50205c0891f_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:56:55.115075+00:00
-- url     : https://prove2.me/theorems/50f5601b-e154-4acb-9deb-d7586c738d35
-- title:
--   A spanning forest preserves components and has the expected edge count
-- statement:
--   Every finite graph has an acyclic spanning subgraph with the same connected components, whose edge count plus the number of graph components equals the number of vertices. Isolated vertices are included as singleton components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

set_option autoImplicit false

theorem WilliamsonShmoys_planar_drawing_spanning_forest__p2m_1ef7e65a_ff27_4a11_b32b_f50205c0891f_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) :
    ∃ H : SimpleGraph V,
      (∀ u v, H.Adj u v → G.Adj u v) ∧
      H.IsAcyclic ∧
      (∀ u v, G.Reachable u v → H.Reachable u v) ∧
      H.edgeSet.ncard + Nat.card G.ConnectedComponent = Fintype.card V := by sorry
