-- Prove2me | Theorems.Thm_WilliamsonShmoys_subgraph_edgeSet_ncard_le__p2m_ceffe8f7_0bd7_41ea_898f_3fe9bc8f26e2_a1
-- name    : WilliamsonShmoys.subgraph_edgeSet_ncard_le__p2m_ceffe8f7_0bd7_41ea_898f_3fe9bc8f26e2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T09:06:50.324342+00:00
-- url     : https://prove2.me/theorems/ba5561eb-f0c4-4b1c-978f-3d913a582677
-- title:
--   Edge cardinality is monotone under subgraphs
-- statement:
--   For finite vertex types, the edge-set cardinality of a simple graph is at most that of any graph containing it as a subgraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.subgraph_edgeSet_ncard_le__p2m_ceffe8f7_0bd7_41ea_898f_3fe9bc8f26e2_a1
    {V : Type} [Fintype V]
    (P Q : SimpleGraph V)
    (hPQ : P ≤ Q) :
    P.edgeSet.ncard ≤ Q.edgeSet.ncard := by sorry
