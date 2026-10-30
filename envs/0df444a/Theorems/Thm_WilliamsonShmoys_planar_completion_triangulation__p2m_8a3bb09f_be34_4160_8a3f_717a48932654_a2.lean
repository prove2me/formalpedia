-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_triangulation__p2m_8a3bb09f_be34_4160_8a3f_717a48932654_a2
-- name    : WilliamsonShmoys.planar_completion_triangulation__p2m_8a3bb09f_be34_4160_8a3f_717a48932654_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T03:06:43.874771+00:00
-- url     : https://prove2.me/theorems/16c7c6d3-4c47-4d12-841f-91c35e1891db
-- title:
--   Triangulate a finite drawable graph without adding vertices
-- statement:
--   Every drawable finite simple graph on at least three vertices is a subgraph of a drawable graph on the same vertex set whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_triangulation__p2m_8a3bb09f_be34_4160_8a3f_717a48932654_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun L : SimpleGraph V =>
      (forall {u v}, K.Adj u v -> L.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn L /\
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
