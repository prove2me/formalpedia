-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_aux_20261026
-- name    : WilliamsonShmoys.maximal_planar_edge_count_aux_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:58:28.070377+00:00
-- url     : https://prove2.me/theorems/56af8ecf-34fb-4522-8eea-1b2fcbed28f6
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A planar graph on at least three vertices that has no planar edge extension on the same vertex type has exactly `3|V| - 6` edges. The lower bound `3 ≤ |V|` is essential: it excludes the smaller cases where maximal planar graphs do not have this edge count. An independent proof route is to work with the drawing’s faces, use maximality to establish connectedness and triangular faces, then combine Euler’s formula with face-edge incidence counting. Formalizing those steps for the supplied arc predicate is the remaining topological core obligation; at `|V| = 3`, the conclusion reduces to the triangle case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_aux_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet →
      HasPlanarDrawingOn L →
      K.edgeSet = L.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
