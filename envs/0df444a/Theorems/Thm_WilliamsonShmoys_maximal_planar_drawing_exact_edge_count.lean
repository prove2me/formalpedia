-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count
-- name    : WilliamsonShmoys.maximal_planar_drawing_exact_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:47:55.603117+00:00
-- url     : https://prove2.me/theorems/2b2e9e38-c6ec-4964-89df-ddfe1061db2d
-- title:
--   An inclusion-maximal drawing has the triangulation edge count
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertex type has exactly 3|V|−6 edges. This child removes the planar edge-count argument from the parent. A proof route is to derive Euler’s formula for the finite arc embedding, use maximality to establish connectedness and triangular faces, count face-edge incidences as 3F = 2E, and combine the equations. The boundary |V| = 3 gives the triangle case. Formalizing the embedding, face structure, and Euler count is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hKmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
