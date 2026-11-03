-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_d2e6787a_41a9_4272_bec1_4c170f4b8b09_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_d2e6787a_41a9_4272_bec1_4c170f4b8b09_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:31:48.135775+00:00
-- url     : https://prove2.me/theorems/f8b110d8-67db-4582-b9bf-9e52697d207d
-- title:
--   Planar triangulation extension edge count
-- statement:
--   Any graph with the specified crossing-free drawing on a finite ordered vertex type of size at least three has a drawable supergraph on the same vertex type whose edge count is three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_d2e6787a_41a9_4272_bec1_4c170f4b8b09_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ S : SimpleGraph V, R ≤ S ∧ WilliamsonShmoys.HasPlanarDrawingOn S ∧
      (letI : DecidableRel S.Adj := Classical.decRel S.Adj
       S.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
