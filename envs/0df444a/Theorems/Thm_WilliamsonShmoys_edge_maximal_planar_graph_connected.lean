-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_connected
-- name    : WilliamsonShmoys.edge_maximal_planar_graph_connected
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:52:46.30416+00:00
-- url     : https://prove2.me/theorems/0d191870-f229-447a-baf8-632074ce239d
-- title:
--   An edge maximal planar supergraph is connected
-- statement:
--   A planar graph on at least three vertices that has maximum edge count among its planar supergraphs on the same vertices is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_graph_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet.ncard ≤ H.edgeSet.ncard) :
    ∀ u v, Relation.ReflTransGen H.Adj u v := by sorry
