-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_triangulation_count_3624186a_b460_4cf9_8afd_86ec1a2d5ee8
-- name    : WilliamsonShmoys.maximal_planar_graph_triangulation_count_3624186a_b460_4cf9_8afd_86ec1a2d5ee8
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T07:28:16.634681+00:00
-- url     : https://prove2.me/theorems/b5c59d06-a2ae-4d81-aa2e-9c766cca4200
-- title:
--   Euler and triangulated-face count for maximal drawable graphs
-- statement:
--   A finite maximal drawable simple graph with at least three vertices admits a face count satisfying Euler’s equation and the exact edge-face incidence count for triangular faces. Euler’s equation and this incidence equality imply the target edge lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_triangulation_count_3624186a_b460_4cf9_8afd_86ec1a2d5ee8
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ->
      Set.Subset N.edgeSet K.edgeSet ->
      N.edgeSet = K.edgeSet)
    (hV : 3 <= Fintype.card V) :
    exists f : Nat,
      Fintype.card V + f = N.edgeSet.ncard + 2 /\
      2 * N.edgeSet.ncard = 3 * f := by sorry
