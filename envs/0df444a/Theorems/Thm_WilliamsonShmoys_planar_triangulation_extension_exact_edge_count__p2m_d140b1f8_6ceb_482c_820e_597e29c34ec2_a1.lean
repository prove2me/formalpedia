-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_exact_edge_count__p2m_d140b1f8_6ceb_482c_820e_597e29c34ec2_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension_exact_edge_count__p2m_d140b1f8_6ceb_482c_820e_597e29c34ec2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:06:56.574448+00:00
-- url     : https://prove2.me/theorems/f99c5cac-36e0-4790-ada9-7e137313e2a6
-- title:
--   Triangulation extension with exact planar edge count
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension_exact_edge_count__p2m_d140b1f8_6ceb_482c_820e_597e29c34ec2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
