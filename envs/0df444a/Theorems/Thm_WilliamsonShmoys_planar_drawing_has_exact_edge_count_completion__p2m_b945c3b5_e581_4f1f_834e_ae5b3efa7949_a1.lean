-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion__p2m_b945c3b5_e581_4f1f_834e_ae5b3efa7949_a1
-- name    : WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_b945c3b5_e581_4f1f_834e_ae5b3efa7949_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:19:42.082354+00:00
-- url     : https://prove2.me/theorems/0d4fbf3e-ba5d-4358-a028-c1fcc85193dd
-- title:
--   Exact edge-count completion of a planar drawing
-- statement:
--   Every drawable finite simple graph on at least three vertices extends, on the same vertex set, to a drawable graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_b945c3b5_e581_4f1f_834e_ae5b3efa7949_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
