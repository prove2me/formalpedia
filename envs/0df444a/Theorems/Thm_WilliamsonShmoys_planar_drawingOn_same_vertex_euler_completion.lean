-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_same_vertex_euler_completion
-- name    : WilliamsonShmoys.planar_drawingOn_same_vertex_euler_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T10:14:00.045612+00:00
-- url     : https://prove2.me/theorems/09e79d85-6f2e-4efd-9ead-ae485c166487
-- title:
--   Complete a planar drawing on the same vertex set
-- statement:
--   A finite graph with at least three vertices and a crossing-free drawing can be extended, without adding vertices, to a planar graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_same_vertex_euler_completion {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hV : 3 ≤ Fintype.card V) : ∃ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N ∧ M.edgeSet ⊆ N.edgeSet ∧ 3 * Fintype.card V = N.edgeSet.ncard + 6 := by sorry
