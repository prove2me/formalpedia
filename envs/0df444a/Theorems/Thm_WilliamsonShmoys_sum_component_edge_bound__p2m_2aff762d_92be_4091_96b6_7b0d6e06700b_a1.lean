-- Prove2me | Theorems.Thm_WilliamsonShmoys_sum_component_edge_bound__p2m_2aff762d_92be_4091_96b6_7b0d6e06700b_a1
-- name    : WilliamsonShmoys.sum_component_edge_bound__p2m_2aff762d_92be_4091_96b6_7b0d6e06700b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:27:27.150986+00:00
-- url     : https://prove2.me/theorems/1501895e-8d06-4c19-968a-5139d07078f6
-- title:
--   Aggregate connected-component edge bounds
-- statement:
--   If a finite family of vertex sets accounts exactly for the graph's vertex and edge counts, each induced graph in the family is connected, small members have the simple-graph edge bound, and members of size at least three satisfy the six-slack hypothesis, then the whole graph satisfies the six-slack bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.sum_component_edge_bound__p2m_2aff762d_92be_4091_96b6_7b0d6e06700b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hcomponents : ∀ (W : Finset V), 3 ≤ W.card →
      (M.induce (W : Set V)).Connected →
      (M.induce (W : Set V)).edgeSet.ncard + 6 ≤ 3 * W.card)
    (parts : Finset (Finset V))
    (hcard : Fintype.card V = ∑ W ∈ parts, W.card)
    (hedges : M.edgeSet.ncard =
      ∑ W ∈ parts, (M.induce (W : Set V)).edgeSet.ncard)
    (hconn : ∀ W ∈ parts, (M.induce (W : Set V)).Connected)
    (hsmall : ∀ W ∈ parts, W.card < 3 →
      (M.induce (W : Set V)).edgeSet.ncard ≤ W.card - 1) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
