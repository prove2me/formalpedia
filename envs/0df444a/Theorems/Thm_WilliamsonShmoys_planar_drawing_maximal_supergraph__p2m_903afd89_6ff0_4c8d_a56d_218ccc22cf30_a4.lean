-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_903afd89_6ff0_4c8d_a56d_218ccc22cf30_a4
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_903afd89_6ff0_4c8d_a56d_218ccc22cf30_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:48:33.598738+00:00
-- url     : https://prove2.me/theorems/3e2bcc8c-0c01-4e2a-b8cc-6b7ae84ea1ec
-- title:
--   Extend a planar drawing to an edge-maximal planar supergraph
-- statement:
--   Every finite planar graph has a same-vertex planar supergraph maximal among planar supergraphs, with at least as many edges as the original. The argument selects a planar supergraph containing M with greatest edge count among the finitely many graphs on V; any planar supergraph containing that choice must have the same edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_903afd89_6ff0_4c8d_a56d_218ccc22cf30_a4 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) : ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧ M.edgeSet.ncard ≤ N.edgeSet.ncard ∧ (∀ Q : SimpleGraph V, N ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q ≤ N) := by sorry
