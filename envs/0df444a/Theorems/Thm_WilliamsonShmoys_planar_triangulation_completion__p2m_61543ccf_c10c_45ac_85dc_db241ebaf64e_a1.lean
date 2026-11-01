-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_61543ccf_c10c_45ac_85dc_db241ebaf64e_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_61543ccf_c10c_45ac_85dc_db241ebaf64e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:01:28.171377+00:00
-- url     : https://prove2.me/theorems/8b27cfb4-0f8b-46ed-98a5-9ae477e5a402
-- title:
--   Same-vertex-set triangulation completion
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges. The extension allows disconnected input graphs and isolated vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_61543ccf_c10c_45ac_85dc_db241ebaf64e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G <= K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
