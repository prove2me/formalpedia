-- Prove2me | Theorems.Thm_strict_supergraph_of_planar_edge_count_gap__p2m_d8aa4474_1bb0_4a8a_92a2_795d49f289c9_a1
-- name    : strict_supergraph_of_planar_edge_count_gap__p2m_d8aa4474_1bb0_4a8a_92a2_795d49f289c9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:46:19.110433+00:00
-- url     : https://prove2.me/theorems/fd97a6dc-1142-4fdf-9191-f45de51a19a7
-- title:
--   A strict planar edge-count gap forces a strict extension
-- statement:
--   If \(K\) is a subgraph of \(L\), the edge count of \(K\) is strictly below the triangulation count, and \(L\) has that count, then \(L\) is not a subgraph of \(K\).
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem strict_supergraph_of_planar_edge_count_gap__p2m_d8aa4474_1bb0_4a8a_92a2_795d49f289c9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K L : SimpleGraph V)
    (dK : DecidableRel K.Adj)
    (hKL : K ≤ L)
    (hsmall : (letI : DecidableRel K.Adj := dK
      K.edgeFinset.card < 3 * Fintype.card V - 6))
    (hcount : (letI : DecidableRel L.Adj := Classical.decRel L.Adj
      L.edgeFinset.card = 3 * Fintype.card V - 6)) :
    ¬ L ≤ K := by
  sorry
