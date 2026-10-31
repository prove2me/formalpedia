-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_2bf11b69_7074_453d_b4a4_93e188db5490_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_2bf11b69_7074_453d_b4a4_93e188db5490_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:06:56.768984+00:00
-- url     : https://prove2.me/theorems/d2478348-c72f-40e5-ae45-20f8d99d0e8e
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   An inclusion-maximal graph admitting the specified planar drawing, on at least three vertices, has exactly three times the number of vertices minus six edges. The proof route is to show maximality forces triangular faces and then apply Euler's formula, treating the three-vertex case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_2bf11b69_7074_453d_b4a4_93e188db5490_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hT : HasPlanarDrawingOn T) (hV : 3 <= Fintype.card V) (hmax : ∀ K : SimpleGraph V, HasPlanarDrawingOn K → T ≤ K → K ≤ T) : T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
