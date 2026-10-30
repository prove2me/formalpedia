-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_edge_count_of_inclusion_maximality
-- name    : WilliamsonShmoys.planar_drawable_maximal_edge_count_of_inclusion_maximality
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:35:59.64681+00:00
-- url     : https://prove2.me/theorems/0ce3799b-79d1-479a-9774-2359ef9b1bb6
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that admits no proper drawable supergraph on the same vertices has exactly `3|V|-6` edges. Maximality forces triangular faces; Euler’s formula and counting face-edge incidences yield the stated count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_maximal_edge_count_of_inclusion_maximality
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ S : SimpleGraph V,
      (∀ {u v}, R.Adj u v → S.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn S → S = R) :
    R.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
