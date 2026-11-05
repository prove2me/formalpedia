-- Prove2me | Theorems.Thm_WilliamsonShmoys_graph_order_card_facts__p2m_78898e31_8773_419c_99b2_d8837842d221_a2
-- name    : WilliamsonShmoys.graph_order_card_facts__p2m_78898e31_8773_419c_99b2_d8837842d221_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:28:56.761822+00:00
-- url     : https://prove2.me/theorems/040a8aa1-bba1-4f35-aade-86f76384a9e8
-- title:
--   Graph inclusion and finite edge-set cardinalities
-- statement:
--   For simple graphs on a finite vertex type, graph inclusion implies monotonicity of the edge-set cardinality; if the cardinalities are equal under inclusion, the graphs are equal. The proof uses edge-set inclusion, finite-set cardinality, and graph extensionality. This step does not depend on planarity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.graph_order_card_facts__p2m_78898e31_8773_419c_99b2_d8837842d221_a2
    {V : Type} [Fintype V]
    (M N : SimpleGraph V) (hMN : M ≤ N) :
    M.edgeSet.ncard ≤ N.edgeSet.ncard ∧
      (M.edgeSet.ncard = N.edgeSet.ncard → M = N) := by sorry
