-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_edge_count_for_maximal_face_decomposition_2218dce211984abc9cb0bb5b50a2d3f4
-- name    : WilliamsonShmoys.planar_triangulation_completion_edge_count_for_maximal_face_decomposition_2218dce211984abc9cb0bb5b50a2d3f4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:28:59.56727+00:00
-- url     : https://prove2.me/theorems/f15616f1-a7af-4bda-bd21-ea5d91d23182
-- title:
--   Drawable graphs admit a maximal-edge planar completion
-- statement:
--   Every finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3n−6 edges. The boundary case n=3 is completed by the triangle. For larger vertex sets, extend to an inclusion-maximal drawable graph, show its faces are triangular, and count by Euler's formula and face-edge incidences. This is the remaining topological core of the reduction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_completion_edge_count_for_maximal_face_decomposition_2218dce211984abc9cb0bb5b50a2d3f4
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
