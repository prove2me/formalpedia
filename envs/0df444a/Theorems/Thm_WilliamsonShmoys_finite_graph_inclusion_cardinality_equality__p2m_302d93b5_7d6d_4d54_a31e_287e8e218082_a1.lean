-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_inclusion_cardinality_equality__p2m_302d93b5_7d6d_4d54_a31e_287e8e218082_a1
-- name    : WilliamsonShmoys.finite_graph_inclusion_cardinality_equality__p2m_302d93b5_7d6d_4d54_a31e_287e8e218082_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:42:42.690668+00:00
-- url     : https://prove2.me/theorems/49cad5ca-e305-44e7-92bf-cf28640d30a1
-- title:
--   Inclusion and edge-count bound force graph equality
-- statement:
--   For finite graphs on the same vertex type, inclusion H ≤ J and the reverse inequality on finite edge-set cardinalities imply H = J. Inclusion gives edge-set inclusion; since both edge sets are finite, the cardinality bound forces equality of edge sets, and therefore graph equality. This removes the cardinality and extensionality step from the parent. The argument also holds when V is empty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_graph_inclusion_cardinality_equality__p2m_302d93b5_7d6d_4d54_a31e_287e8e218082_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H J : SimpleGraph V) (hHJ : H ≤ J)
    (hcard : J.edgeSet.ncard ≤ H.edgeSet.ncard) : J = H := by sorry
