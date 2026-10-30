-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_completion
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:39:51.991504+00:00
-- url     : https://prove2.me/theorems/78beab53-01eb-4f28-b59a-92d0a9901616
-- title:
--   Drawable completion with the planar edge bound attained
-- statement:
--   Every drawable simple graph on at least three vertices is a subgraph of a drawable graph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  sorry
