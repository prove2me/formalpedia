-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_533c1536_70f9_4baf_8d8d_aa7e4273cff9_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_533c1536_70f9_4baf_8d8d_aa7e4273cff9_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:52:45.59921+00:00
-- url     : https://prove2.me/theorems/a7b1543f-eb9f-42ef-b47d-96ddc7610efd
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite vertices has exactly 3|V| - 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_533c1536_70f9_4baf_8d8d_aa7e4273cff9_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
