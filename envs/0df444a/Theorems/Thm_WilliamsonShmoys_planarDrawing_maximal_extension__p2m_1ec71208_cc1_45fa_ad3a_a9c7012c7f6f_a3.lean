-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_maximal_extension__p2m_1ec71208_cc1_45fa_ad3a_a9c7012c7f6f_a3
-- name    : WilliamsonShmoys.planarDrawing_maximal_extension__p2m_1ec71208_cc1_45fa_ad3a_a9c7012c7f6f_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:50:24.126425+00:00
-- url     : https://prove2.me/theorems/f28d325a-badb-43f7-b5e1-caa5a9a8c825
-- title:
--   Maximal drawable extension on the same vertices
-- statement:
--   A connected drawable graph on at least three vertices has an inclusion-maximal drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawing_maximal_extension__p2m_1ec71208_cc1_45fa_ad3a_a9c7012c7f6f_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ K : SimpleGraph V, H ≤ K →
          WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  sorry
