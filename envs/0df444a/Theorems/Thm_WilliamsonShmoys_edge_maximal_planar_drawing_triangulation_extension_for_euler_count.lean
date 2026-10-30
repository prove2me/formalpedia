-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_triangulation_extension_for_euler_count
-- name    : WilliamsonShmoys.edge_maximal_planar_drawing_triangulation_extension_for_euler_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:52:21.5354+00:00
-- url     : https://prove2.me/theorems/304f8fa5-790a-4081-b498-6c0918c5b6f9
-- title:
--   Triangulation extension for an edge-maximal Euler count
-- statement:
--   A finite graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn has a drawable supergraph on the same vertices with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_drawing_triangulation_extension_for_euler_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
