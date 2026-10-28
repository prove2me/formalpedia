-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_lower_edge_count
-- name    : WilliamsonShmoys.planar_drawing_supergraph_lower_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T06:32:29.639234+00:00
-- url     : https://prove2.me/theorems/89f7b2e6-a389-4b68-b3bd-779ea943bf14
-- title:
--   Drawable supergraph with the planar lower edge bound
-- statement:
--   Every drawable graph on at least three vertices is contained in a drawable graph on the same vertex type whose edge count is at least 3|V|−6. This isolates the geometric augmentation argument. Extend the drawing by adding noncrossing edges until it is maximal, and apply the Euler formula and triangular-face count. The task’s hard remaining obligation is formalizing this route from HasPlanarDrawingOn.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_supergraph_lower_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
