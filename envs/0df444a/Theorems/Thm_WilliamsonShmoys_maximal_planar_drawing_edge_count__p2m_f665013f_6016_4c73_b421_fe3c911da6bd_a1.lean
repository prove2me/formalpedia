-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_f665013f_6016_4c73_b421_fe3c911da6bd_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_f665013f_6016_4c73_b421_fe3c911da6bd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:04:55.825044+00:00
-- url     : https://prove2.me/theorems/742e15ee-6999-43aa-960c-9e8cbc35dbfd
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite vertices has exactly 3|V|−6 edges. The proof route is to derive connectivity and triangular faces from maximality, then combine Euler’s formula with face-edge incidence counting. The at-least-three hypothesis handles the small boundary case; disconnected graphs are excluded from the maximal case because drawable edges can be added between components. This child contains the main topological and Euler-counting obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_f665013f_6016_4c73_b421_fe3c911da6bd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
