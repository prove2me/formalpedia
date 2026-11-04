-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulation_edge_count__p2m_bc67589b_3983_4963_b1d8_6aabd3b931c4_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_triangulation_edge_count__p2m_bc67589b_3983_4963_b1d8_6aabd3b931c4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:14:37.012576+00:00
-- url     : https://prove2.me/theorems/757b64a4-4ecc-451f-8c8e-f98c58cc600e
-- title:
--   An inclusion-maximal planar drawing has the triangulation edge count
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. The proof must handle disconnected drawings and the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_has_triangulation_edge_count__p2m_bc67589b_3983_4963_b1d8_6aabd3b931c4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      3 * Fintype.card V = L.edgeFinset.card + 6) := by sorry
