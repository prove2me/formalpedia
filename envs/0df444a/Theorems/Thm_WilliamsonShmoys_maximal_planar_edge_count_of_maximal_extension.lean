-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_of_maximal_extension
-- name    : WilliamsonShmoys.maximal_planar_edge_count_of_maximal_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T00:24:33.451934+00:00
-- url     : https://prove2.me/theorems/842a9801-a8ab-4947-940f-512d60f56b7a
-- title:
--   Maximal planar graphs have the triangulation edge count
-- statement:
--   A graph with the specified planar drawing that is inclusion-maximal among planar supergraphs on the same vertices, and has at least three vertices, has exactly three times the number of vertices minus six edges. The proof route is to show every face of a maximal planar embedding is triangular, then apply Euler’s formula. The condition of at least three vertices covers the smallest case, the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_of_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L ≤ K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
