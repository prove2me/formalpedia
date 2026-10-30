-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_edge_count
-- name    : WilliamsonShmoys.edge_maximal_planar_drawing_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:57:56.284965+00:00
-- url     : https://prove2.me/theorems/19a1efb7-fe55-48e3-b87b-da9613e3ac3a
-- title:
--   Edge count of an edge-maximal planar drawing
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_drawing_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
