-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_separate_components__p2m_8e313f52_7cd9_446d_9cbb_05951652d57f_a3
-- name    : WilliamsonShmoys.planar_drawing_add_edge_between_separate_components__p2m_8e313f52_7cd9_446d_9cbb_05951652d57f_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:57:44.477216+00:00
-- url     : https://prove2.me/theorems/d4f3926c-49e7-4844-9217-e73e41032d89
-- title:
--   Extend a planar drawing by an edge between unreachable vertices
-- statement:
--   For a finite ordered vertex type, a graph with a planar drawing, and two unreachable vertices, there is a graph extension containing their edge that still has a planar drawing. Unreachability rules out the equality boundary u = v. This isolates the geometric re-embedding construction; the parent derives strictness from the added adjacency.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_edge_between_separate_components__p2m_8e313f52_7cd9_446d_9cbb_05951652d57f_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    {u v : V} (hUnreachable : ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ K.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  sorry
