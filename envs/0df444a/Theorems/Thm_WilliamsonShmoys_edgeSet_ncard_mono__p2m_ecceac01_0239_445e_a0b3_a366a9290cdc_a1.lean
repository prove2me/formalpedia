-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_ecceac01_0239_445e_a0b3_a366a9290cdc_a1
-- name    : WilliamsonShmoys.edgeSet_ncard_mono__p2m_ecceac01_0239_445e_a0b3_a366a9290cdc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:28:20.829995+00:00
-- url     : https://prove2.me/theorems/75ca471a-15b8-431f-8a78-0fb60a6ca5a2
-- title:
--   Edge cardinality is monotone under subgraphs
-- statement:
--   For finite simple graphs on the same vertex type, taking a subgraph cannot increase the edge-set cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_mono__p2m_ecceac01_0239_445e_a0b3_a366a9290cdc_a1 {V : Type} [Fintype V] (G H : SimpleGraph V) (h : G ≤ H) : G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
