-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_exists__p2m_d07e54eb_c4bc_460d_b7df_6d44fa14b7ac_a1
-- name    : WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_d07e54eb_c4bc_460d_b7df_6d44fa14b7ac_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:47:42.760929+00:00
-- url     : https://prove2.me/theorems/989b9ffa-ac83-4205-b86c-4def2f85e45f
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable graph on the same vertices that has no proper drawable supergraph. The finite maximization route is to choose a drawable supergraph with the largest edge set; the boundary conditions include disconnected graphs and do not require at least three vertices. This removes the existence and maximality selection from the parent. It does not establish the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_d07e54eb_c4bc_460d_b7df_6d44fa14b7ac_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, ∃ dH : DecidableRel H.Adj,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧ G ≤ H ∧
      ∀ K : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn K → H ≤ K → K = H := by sorry
