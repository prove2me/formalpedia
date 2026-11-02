-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension__p2m_3b1a98e5_f0d3_4027_b8f6_4e4c1f675a8e_a1
-- name    : WilliamsonShmoys.exists_planar_triangulation_extension__p2m_3b1a98e5_f0d3_4027_b8f6_4e4c1f675a8e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:57:43.271457+00:00
-- url     : https://prove2.me/theorems/d8587c1f-e0c9-4a1c-96ac-f198f2c65871
-- title:
--   Triangulated planar extension on the same vertices
-- statement:
--   Every connected graph with a crossing-free drawing and at least three vertices has a planar supergraph on the same vertices whose edge count is three times the number of vertices minus six. The edge-count assertion is stated for any decidable adjacency instance on the extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_triangulation_extension__p2m_3b1a98e5_f0d3_4027_b8f6_4e4c1f675a8e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hconn : N.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ P : SimpleGraph V, N ≤ P ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      ∀ [DecidableRel P.Adj],
        P.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
