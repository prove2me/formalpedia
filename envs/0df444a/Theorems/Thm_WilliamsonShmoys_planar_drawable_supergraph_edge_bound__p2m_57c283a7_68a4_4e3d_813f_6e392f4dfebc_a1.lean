-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_supergraph_edge_bound__p2m_57c283a7_68a4_4e3d_813f_6e392f4dfebc_a1
-- name    : WilliamsonShmoys.planar_drawable_supergraph_edge_bound__p2m_57c283a7_68a4_4e3d_813f_6e392f4dfebc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:05:37.238108+00:00
-- url     : https://prove2.me/theorems/4f14f4e8-9a22-49bc-9255-581b0400575d
-- title:
--   Drawable supergraph with planar edge lower bound
-- statement:
--   Every drawable graph on at least three vertices is contained in a drawable graph on the same vertex set with at least 3|V|−6 edges. Choose a drawable supergraph maximal among the finitely many supergraphs on V; adding edges across non-triangular faces and joining components shows that it is a triangulation. Euler’s formula and counting face-edge incidences give the edge bound. This isolates the topological completion and counting argument from the parent’s use of maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawable_supergraph_edge_bound__p2m_57c283a7_68a4_4e3d_813f_6e392f4dfebc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, HasPlanarDrawingOn N ∧ M ≤ N ∧
      ∀ [DecidableRel N.Adj], 3 * Fintype.card V - 6 ≤ N.edgeFinset.card := by sorry
