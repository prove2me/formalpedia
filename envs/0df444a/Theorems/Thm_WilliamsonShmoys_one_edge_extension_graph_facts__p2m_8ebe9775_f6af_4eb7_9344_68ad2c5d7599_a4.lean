-- Prove2me | Theorems.Thm_WilliamsonShmoys_one_edge_extension_graph_facts__p2m_8ebe9775_f6af_4eb7_9344_68ad2c5d7599_a4
-- name    : WilliamsonShmoys.one_edge_extension_graph_facts__p2m_8ebe9775_f6af_4eb7_9344_68ad2c5d7599_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:49:51.849427+00:00
-- url     : https://prove2.me/theorems/f8698c3a-ced4-475a-9208-664e8ed30927
-- title:
--   The one-edge extension strictly increases the edge count
-- statement:
--   Adding the unordered edge between distinct unreachable vertices gives a supergraph and strictly increases the finite edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.one_edge_extension_graph_facts__p2m_8ebe9775_f6af_4eb7_9344_68ad2c5d7599_a4
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (u v : V) (huv : u ≠ v) (hUnreachable : ¬ N.Reachable u v) :
    let K : SimpleGraph V :=
      N ⊔ SimpleGraph.fromRel (fun a b => a = u ∧ b = v)
    N ≤ K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : DecidableRel N.Adj := Classical.decRel N.Adj
       N.edgeFinset.card < K.edgeFinset.card) := by sorry
