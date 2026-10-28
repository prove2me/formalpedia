-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_via_faces
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_via_faces
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T03:16:13.382393+00:00
-- url     : https://prove2.me/theorems/4c4a6dd5-1ee4-43ce-a7d3-88e29dce7c03
-- title:
--   Planar edge upper bound by face counting
-- statement:
--   A graph with the supplied crossing-free drawing and at least three vertices has at most 3|V| − 6 edges. Prove this by Euler counting and the simple planar face-incidence bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_via_faces
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
