-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_supergraph_bound
-- name    : WilliamsonShmoys.planar_edge_supergraph_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T13:49:26.262762+00:00
-- url     : https://prove2.me/theorems/1a1e4639-984e-4d53-99b4-0a5c82fb99e6
-- title:
--   Planar supergraph edge bound
-- statement:
--   A connected graph on at least three finite linearly ordered vertices with the packaged crossing-free drawing has a simple planar supergraph on the same vertices whose edge count is at most three times the vertex count minus six. Prove by extending the drawing with noncrossing edges to a maximal planar drawing, then applying Euler’s formula and the face-boundary count. This isolates the geometric extension and counting work; those remain the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_supergraph_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hConn : forall u v, Relation.ReflTransGen J.Adj u v)
    (hV : 3 <= Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V,
      J.edgeSet ⊆ K.edgeSet ∧
      K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
