-- Prove2me | Theorems.Thm_simpleGraph_extension_card_le_reverse__p2m_4ae5c893_7e52_474c_915d_3ed4ab7c0e94_a1
-- name    : simpleGraph_extension_card_le_reverse__p2m_4ae5c893_7e52_474c_915d_3ed4ab7c0e94_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:29:35.395297+00:00
-- url     : https://prove2.me/theorems/7e17c62a-a30b-4bcd-becf-bea420b21f47
-- title:
--   Finite graph inclusion from an edge-count bound
-- statement:
--   For simple graphs on a finite vertex type, if H is a subgraph of G and G has no more edges than H, then G is also a subgraph of H. The finite edge sets are nested, so the cardinality bound forces equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem simpleGraph_extension_card_le_reverse__p2m_4ae5c893_7e52_474c_915d_3ed4ab7c0e94_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H G : SimpleGraph V)
    (hHG : H ≤ G)
    (hcard :
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       letI : DecidableRel G.Adj := Classical.decRel G.Adj
       G.edgeFinset.card ≤ H.edgeFinset.card)) : G ≤ H := by sorry
