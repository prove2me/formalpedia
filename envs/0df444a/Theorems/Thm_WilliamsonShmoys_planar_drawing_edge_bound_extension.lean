-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_extension
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T05:25:16.741555+00:00
-- url     : https://prove2.me/theorems/562ccfc8-3a11-4c46-915d-a6da5fbeedd6
-- title:
--   Planar supergraph edge bound
-- statement:
--   A finite graph with the specified planar drawing and at least three vertices has a planar supergraph on the same vertex type with at least 3|V|−6 edges. Applying the parent’s maximality hypothesis to this supergraph gives the target bound for N.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
