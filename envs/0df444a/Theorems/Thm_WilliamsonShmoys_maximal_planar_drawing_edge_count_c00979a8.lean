-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_c00979a8
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_c00979a8
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:52:16.633387+00:00
-- url     : https://prove2.me/theorems/a3f9912a-5af5-4400-ae1c-df785653929e
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A maximal graph under the supplied arc-based drawing predicate, on at least three vertices, has exactly `3 * |V| - 6` edges. This isolates the geometric work needed after the parent selects a maximal extension. A proof route is to derive connectedness and triangular faces from maximality, establish Euler’s formula for the resulting planar embedding, and count incidences between faces and edges. The three-vertex boundary gives a triangle and satisfies the stated equation; preserving the lower bound is essential because the formula does not hold for maximal planar graphs on fewer vertices. Formalizing the drawing-to-embedding and face-count steps is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_c00979a8 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hmax : ∀ L : SimpleGraph V, K <= L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) : 3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
