-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_d6e88113
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_d6e88113
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T02:24:20.047582+00:00
-- url     : https://prove2.me/theorems/ddd06cd1-c897-4f8f-92e2-6dba265242d3
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A connected drawable simple graph on at least three vertices that has no proper drawable supergraph on the same vertex type has exactly 3|V|−6 edges. Prove this using Euler’s formula and the fact that maximality forces triangular faces; the face-boundary details for the concrete drawing predicate remain the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_d6e88113
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn K) (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, HasPlanarDrawingOn L → K ≤ L → L ≤ K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
