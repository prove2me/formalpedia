-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count_d6e88113
-- name    : WilliamsonShmoys.planar_completion_edge_count_d6e88113
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T02:46:09.61973+00:00
-- url     : https://prove2.me/theorems/e4624ca0-ee5d-48b7-9015-29f38862bd05
-- title:
--   Drawable completion with maximal planar edge count
-- statement:
--   Every finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges. The statement covers disconnected graphs and the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_edge_count_d6e88113
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, HasPlanarDrawingOn L ∧ K ≤ L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
