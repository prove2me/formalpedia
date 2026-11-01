-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_7b77c23b_62df_4ae5_b586_caedc2314578_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_7b77c23b_62df_4ae5_b586_caedc2314578_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:07:47.379199+00:00
-- url     : https://prove2.me/theorems/ac7ad3d7-f745-41b8-8bbb-a0b9a0b84694
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A maximal planar simple graph on a finite ordered vertex type with at least three vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_7b77c23b_62df_4ae5_b586_caedc2314578_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
