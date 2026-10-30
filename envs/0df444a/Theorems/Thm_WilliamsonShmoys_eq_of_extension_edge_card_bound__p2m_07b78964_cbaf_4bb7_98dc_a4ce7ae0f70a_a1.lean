-- Prove2me | Theorems.Thm_WilliamsonShmoys_eq_of_extension_edge_card_bound__p2m_07b78964_cbaf_4bb7_98dc_a4ce7ae0f70a_a1
-- name    : WilliamsonShmoys.eq_of_extension_edge_card_bound__p2m_07b78964_cbaf_4bb7_98dc_a4ce7ae0f70a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:57:10.657465+00:00
-- url     : https://prove2.me/theorems/aef3d10b-07fc-4a9b-a9f4-75a3a8b305ef
-- title:
--   Equality from edge inclusion and cardinality
-- statement:
--   For graphs on a finite vertex type, if N is a subgraph of K and K has no more edges than N, then K and N are equal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.eq_of_extension_edge_card_bound__p2m_07b78964_cbaf_4bb7_98dc_a4ce7ae0f70a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N K : SimpleGraph V)
    (hNK : N ≤ K)
    (hCard : K.edgeSet.ncard ≤ N.edgeSet.ncard) :
    K = N := by sorry
