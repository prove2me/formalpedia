-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_1cb61011_99ad_4f9a_a1ee_f080a0059de3_a2
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_1cb61011_99ad_4f9a_a1ee_f080a0059de3_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:19:18.496195+00:00
-- url     : https://prove2.me/theorems/84e3af3d-8b6d-4d30-bf7d-46baabad1e1c
-- title:
--   Exact edge-count planar completion
-- statement:
--   Any graph with the specified planar drawing on a finite ordered vertex type of at least three vertices has a drawable supergraph on the same vertex type whose edge count is exactly three times the number of vertices minus six. The parent applies maximality to identify that supergraph with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_1cb61011_99ad_4f9a_a1ee_f080a0059de3_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    ∃ M : SimpleGraph V, L <= M ∧ HasPlanarDrawingOn M ∧
      (letI : DecidableRel M.Adj := Classical.decRel M.Adj
       M.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
