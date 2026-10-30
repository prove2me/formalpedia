-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_exact_edge_count_completion__p2m_60b38c6b_3179_48fe_bb14_f21b6e8b7c6f_a1
-- name    : WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_60b38c6b_3179_48fe_bb14_f21b6e8b7c6f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:14:48.773049+00:00
-- url     : https://prove2.me/theorems/0e3a5bf5-c35e-4938-9aa7-a032ab0de182
-- title:
--   Exact edge-count completion of a drawable graph
-- statement:
--   Every drawable finite simple graph on at least three vertices extends on the same vertex type to a drawable graph with exactly 3|V|−6 edges. Applied to a maximal graph, the extension must equal the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_60b38c6b_3179_48fe_bb14_f21b6e8b7c6f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
