-- Prove2me | Theorems.Thm_WilliamsonShmoys_sup_inserted_nonedge_has_more_edges__p2m_468912c8_f62d_4992_8d85_065aef654ab4_a1__p2m_468912c8_f62d_4992_8d85_065aef654ab4_a2
-- name    : WilliamsonShmoys.sup_inserted_nonedge_has_more_edges__p2m_468912c8_f62d_4992_8d85_065aef654ab4_a1__p2m_468912c8_f62d_4992_8d85_065aef654ab4_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:31:46.647774+00:00
-- url     : https://prove2.me/theorems/e7e1c57c-5481-45ad-9b76-be182d4806e2
-- title:
--   Adding a missing non-loop edge increases the edge count
-- statement:
--   Adding the previously absent edge {u,v}, with u < v, strictly increases the finite edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.sup_inserted_nonedge_has_more_edges__p2m_468912c8_f62d_4992_8d85_065aef654ab4_a1__p2m_468912c8_f62d_4992_8d85_065aef654ab4_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (u v : V) (huv : u < v) (hnot : ¬ G.Adj u v) : G.edgeSet.ncard < (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).edgeSet.ncard := by sorry
