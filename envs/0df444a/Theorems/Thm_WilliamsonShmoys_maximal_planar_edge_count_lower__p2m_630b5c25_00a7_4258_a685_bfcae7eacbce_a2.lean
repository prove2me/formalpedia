-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_630b5c25_00a7_4258_a685_bfcae7eacbce_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_630b5c25_00a7_4258_a685_bfcae7eacbce_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:43:55.271993+00:00
-- url     : https://prove2.me/theorems/a676df72-8370-487d-8148-6fb0674d69c1
-- title:
--   Maximality gives the extremal planar edge lower bound
-- statement:
--   An inclusion-maximal finite graph with the supplied planar drawing and at least three vertices has at least 3V − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_630b5c25_00a7_4258_a685_bfcae7eacbce_a2 {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by sorry
