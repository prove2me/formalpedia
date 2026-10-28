-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_drawable_graph_edge_count
-- name    : WilliamsonShmoys.edge_maximal_drawable_graph_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T06:53:20.913273+00:00
-- url     : https://prove2.me/theorems/d6da05f6-115d-482a-b62f-046e378a3885
-- title:
--   Edge count of an edge-maximal drawable graph
-- statement:
--   An edge-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. The boundary case |V| = 3 gives three edges. A proof route is to interpret the supplied drawing as a plane embedding, show maximality forces every face to be triangular (including by adding edges between components or across a nontriangular face when possible), and count incidences between faces and edges. Euler’s formula then gives the claimed edge count. This removes the entire planar counting step from the parent; the main remaining obligation is deriving the needed embedding and face properties from HasPlanarDrawingOn and its exact maximality hypothesis.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_drawable_graph_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ W : SimpleGraph V,
      (∀ {u v}, U.Adj u v → W.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn W → W = U) :
    U.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
