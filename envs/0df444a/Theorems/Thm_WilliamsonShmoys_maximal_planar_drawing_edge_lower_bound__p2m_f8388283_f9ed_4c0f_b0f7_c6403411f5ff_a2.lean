-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_f8388283_f9ed_4c0f_b0f7_c6403411f5ff_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_f8388283_f9ed_4c0f_b0f7_c6403411f5ff_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:03:07.67022+00:00
-- url     : https://prove2.me/theorems/726fe57b-9b66-48eb-a490-e0e9926cc417
-- title:
--   Lower bound from maximality and planar completion
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertices has at least 3|V|−6 edges. Extend its drawing to a drawable supergraph with exactly 3|V|−6 edges and use maximality to identify that supergraph with X. At three vertices, the completion is the triangle. The core obligation is proving drawing-preserving completion on the fixed vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_f8388283_f9ed_4c0f_b0f7_c6403411f5ff_a2 {V : Type} [Fintype V] [LinearOrder V] (X : SimpleGraph V) (hX : WilliamsonShmoys.HasPlanarDrawingOn X) (hV : 3 ≤ Fintype.card V) (hmax : ∀ Y : SimpleGraph V, X ≤ Y → WilliamsonShmoys.HasPlanarDrawingOn Y → Y = X) : 3 * Fintype.card V ≤ X.edgeSet.ncard + 6 := by sorry
