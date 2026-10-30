-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_edge_bound__p2m_a3d46af7_d8d1_44e5_ae3d_980c06c923f9_a1
-- name    : WilliamsonShmoys.exists_planar_supergraph_with_edge_bound__p2m_a3d46af7_d8d1_44e5_ae3d_980c06c923f9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T08:35:26.128987+00:00
-- url     : https://prove2.me/theorems/df288277-9c1c-43a5-8845-caf345f4f17a
-- title:
--   Drawable supergraph with the planar edge bound
-- statement:
--   Any drawable simple graph on a finite set of at least three vertices extends, without changing its vertex set, to a drawable supergraph meeting the planar lower bound on edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_supergraph_with_edge_bound__p2m_a3d46af7_d8d1_44e5_ae3d_980c06c923f9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (S : Set V) [Fintype S]
    (G : SimpleGraph S)
    (hDraw : HasPlanarDrawingOn G)
    (hcard : 3 ≤ S.ncard) :
    ∃ N : SimpleGraph S, G ≤ N ∧ HasPlanarDrawingOn N ∧
      3 * S.ncard ≤ N.edgeSet.ncard + 6 := by sorry
