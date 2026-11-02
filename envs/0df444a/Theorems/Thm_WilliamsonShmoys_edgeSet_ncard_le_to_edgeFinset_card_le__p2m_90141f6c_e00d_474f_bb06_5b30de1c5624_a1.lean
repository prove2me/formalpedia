-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_le_to_edgeFinset_card_le__p2m_90141f6c_e00d_474f_bb06_5b30de1c5624_a1
-- name    : WilliamsonShmoys.edgeSet_ncard_le_to_edgeFinset_card_le__p2m_90141f6c_e00d_474f_bb06_5b30de1c5624_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:43:13.380897+00:00
-- url     : https://prove2.me/theorems/c7e16f7d-274a-4fb1-9b3b-8eebfa8dd28e
-- title:
--   Transfer an edge-set bound to the edge finset
-- statement:
--   For a finite graph with a chosen adjacency decision procedure, a bound on the cardinality of its edge set transfers to the cardinality of its edge finset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.edgeSet_ncard_le_to_edgeFinset_card_le__p2m_90141f6c_e00d_474f_bb06_5b30de1c5624_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hbound : K.edgeSet.ncard ≤ 3 * Fintype.card V - 6) :
    (letI : DecidableRel K.Adj := dK;
     K.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
