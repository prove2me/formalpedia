-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_connected__p2m_06914e2b_7aee_4867_807c_e684f2b708fd_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_connected__p2m_06914e2b_7aee_4867_807c_e684f2b708fd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:23:31.638965+00:00
-- url     : https://prove2.me/theorems/bc735298-99fb-476e-aa8d-1e3af7f2e774
-- title:
--   An edge maximal planar graph is connected
-- statement:
--   A finite drawn simple graph with at least three vertices, maximal in edge count among its planar supergraphs on the same vertices, is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_connected__p2m_06914e2b_7aee_4867_807c_e684f2b708fd_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hKplanar : HasPlanarDrawingOn K) (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L.edgeSet.ncard ≤ K.edgeSet.ncard) (hV : 3 ≤ Fintype.card V) : K.Connected := by sorry
