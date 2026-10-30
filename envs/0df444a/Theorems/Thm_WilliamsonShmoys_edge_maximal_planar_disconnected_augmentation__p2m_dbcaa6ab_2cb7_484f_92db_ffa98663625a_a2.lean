-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_disconnected_augmentation__p2m_dbcaa6ab_2cb7_484f_92db_ffa98663625a_a2
-- name    : WilliamsonShmoys.edge_maximal_planar_disconnected_augmentation__p2m_dbcaa6ab_2cb7_484f_92db_ffa98663625a_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:50:47.4085+00:00
-- url     : https://prove2.me/theorems/69c823a1-26ea-4d61-ada1-9ff7bd41c4c8
-- title:
--   Planar edge augmentation of a disconnected graph
-- statement:
--   A disconnected graph on at least three vertices with a crossing-free drawing can be extended, on the same vertices, to a crossing-free drawing of a graph with strictly more edges. The size bound excludes the empty-vertex case; disconnectedness supplies distinct components to join. The proof work is the topological re-embedding of the finitely many components and construction of a joining arc avoiding all other components. The parent uses this strict planar supergraph to contradict maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_disconnected_augmentation__p2m_dbcaa6ab_2cb7_484f_92db_ffa98663625a_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hDisconnected : ¬ H.Connected) : ∃ K : SimpleGraph V, H.edgeSet ⊂ K.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
