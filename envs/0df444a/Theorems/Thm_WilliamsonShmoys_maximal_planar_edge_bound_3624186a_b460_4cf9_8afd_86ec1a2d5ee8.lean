-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_3624186a_b460_4cf9_8afd_86ec1a2d5ee8
-- name    : WilliamsonShmoys.maximal_planar_edge_bound_3624186a_b460_4cf9_8afd_86ec1a2d5ee8
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T06:43:16.625721+00:00
-- url     : https://prove2.me/theorems/429715c4-4b60-4a27-92dc-edf3a3ce7a97
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   A drawable simple graph maximal under edge inclusion on its fixed finite vertex type, with at least three vertices, has at least 3|V| − 6 edges. The size hypothesis includes the boundary case |V| = 3, where a maximal graph is K3 and the inequality is equality. A proof route is to show maximality forces a connected triangulation, establish Euler's formula and that each face contributes three edge incidences, then derive the stated inequality. The substantial remaining work is formalizing these planar-topology facts from the given drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_bound_3624186a_b460_4cf9_8afd_86ec1a2d5ee8
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ->
      Set.Subset N.edgeSet K.edgeSet ->
      N.edgeSet = K.edgeSet)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V <= N.edgeSet.ncard + 6 := by sorry
