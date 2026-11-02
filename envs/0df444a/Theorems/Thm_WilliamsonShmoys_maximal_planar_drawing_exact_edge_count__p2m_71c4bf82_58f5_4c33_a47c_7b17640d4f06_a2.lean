-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count__p2m_71c4bf82_58f5_4c33_a47c_7b17640d4f06_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_71c4bf82_58f5_4c33_a47c_7b17640d4f06_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:40:45.18632+00:00
-- url     : https://prove2.me/theorems/9987107f-9ded-4251-bab3-dd81d8d6e153
-- title:
--   Maximal planar graphs have the exact edge count
-- statement:
--   A finite drawable simple graph on at least three vertices that is maximal under drawable extension has exactly 3|V| − 6 edges. The geometric work is to establish connectedness and triangular faces for a maximal planar drawing, then apply Euler’s formula and count face-edge incidences; the |V| = 3 case is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_71c4bf82_58f5_4c33_a47c_7b17640d4f06_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N <= K → HasPlanarDrawingOn K → K = N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     N.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  sorry
