-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T23:31:55.502635+00:00
-- url     : https://prove2.me/theorems/823ff616-6cf4-40d4-8378-aba3df604ba6
-- title:
--   An edge-maximal planar graph has the triangulation edge bound
-- statement:
--   If a planar graph on at least three vertices has maximum edge count among its planar supergraphs on the same vertices, then it has at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, K.Adj u v → H.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn H →
      H.edgeSet.ncard ≤ K.edgeSet.ncard) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
