-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_d879fe2f_6575_4a1e_b2ae_694852ee5ed8_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_d879fe2f_6575_4a1e_b2ae_694852ee5ed8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:13:26.238983+00:00
-- url     : https://prove2.me/theorems/46cbd439-c8e2-447f-93cf-6418b9c298f0
-- title:
--   Planar drawings extend to triangulations
-- statement:
--   Any finite simple graph with a planar drawing and at least three vertices is contained, on the same vertex set, in a maximal planar graph with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_d879fe2f_6575_4a1e_b2ae_694852ee5ed8_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) (hCard : 3 ≤ Fintype.card V) : ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧ (∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N) ∧ N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
