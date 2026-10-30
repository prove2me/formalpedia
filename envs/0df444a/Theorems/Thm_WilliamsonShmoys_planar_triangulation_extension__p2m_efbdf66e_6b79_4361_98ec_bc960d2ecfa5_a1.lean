-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_efbdf66e_6b79_4361_98ec_bc960d2ecfa5_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_efbdf66e_6b79_4361_98ec_bc960d2ecfa5_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:05:59.476281+00:00
-- url     : https://prove2.me/theorems/ed86bc60-f31a-467f-bd4d-ab190f9b728c
-- title:
--   Extend a finite planar drawing to a triangulation
-- statement:
--   Every drawable finite simple graph on at least three vertices can be extended, without changing its vertex set, to a drawable graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_efbdf66e_6b79_4361_98ec_bc960d2ecfa5_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ 3 * Fintype.card V - 6 = L.edgeSet.ncard := by sorry
