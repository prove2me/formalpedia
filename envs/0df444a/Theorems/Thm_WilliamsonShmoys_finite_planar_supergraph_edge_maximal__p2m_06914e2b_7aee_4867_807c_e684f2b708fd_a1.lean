-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_edge_maximal__p2m_06914e2b_7aee_4867_807c_e684f2b708fd_a1
-- name    : WilliamsonShmoys.finite_planar_supergraph_edge_maximal__p2m_06914e2b_7aee_4867_807c_e684f2b708fd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:23:28.919802+00:00
-- url     : https://prove2.me/theorems/dfeab8e7-c65a-497d-a20d-7cce49bd8d27
-- title:
--   Choose an edge maximal planar extension
-- statement:
--   Any finite drawn graph has a planar supergraph on the same vertices whose edge count is maximal among its planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.finite_planar_supergraph_edge_maximal__p2m_06914e2b_7aee_4867_807c_e684f2b708fd_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hplanar : HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ H.edgeSet.ncard ≤ K.edgeSet.ncard ∧ ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
