-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_d07e54eb_c4bc_460d_b7df_6d44fa14b7ac_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_d07e54eb_c4bc_460d_b7df_6d44fa14b7ac_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:47:48.544897+00:00
-- url     : https://prove2.me/theorems/267a842e-101e-4cf6-b705-d11d92433d33
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   For a finite linearly ordered vertex type with at least three vertices, every drawable graph that has no proper drawable supergraph on the same vertices has exactly 3|V|−6 edges. The lower bound of three vertices is essential to the maximal planar graph count. A proof route is to establish connectedness and triangular faces from maximality for the given drawing notion, then combine Euler's formula with the face-edge incidence count. This isolates the central topological and counting obligation; it does not follow from finite maximization alone.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_d07e54eb_c4bc_460d_b7df_6d44fa14b7ac_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hn : 3 <= Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K → H ≤ K → K = H) :
    (letI : DecidableRel H.Adj := dH;
     H.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
