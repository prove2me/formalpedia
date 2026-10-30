-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_nat_edge_count_completion_maximal_edge_count_553ae5ef
-- name    : WilliamsonShmoys.planar_drawing_has_nat_edge_count_completion_maximal_edge_count_553ae5ef
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:38:04.201572+00:00
-- url     : https://prove2.me/theorems/57ec06b7-68e5-4473-9704-8e33e9567d83
-- title:
--   A maximal drawable graph has the planar triangulation edge count
-- statement:
--   A drawable graph with at least three vertices that is maximal among drawable supergraphs on the same vertices has exactly 3|V|−6 edges. Maximality forces connectedness and triangular faces; Euler’s formula and face-edge incidence yield the equation, including the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_nat_edge_count_completion_maximal_edge_count_553ae5ef
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
