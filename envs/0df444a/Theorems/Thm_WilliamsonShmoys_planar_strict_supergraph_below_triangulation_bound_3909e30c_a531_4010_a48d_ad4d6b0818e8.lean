-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_strict_supergraph_below_triangulation_bound_3909e30c_a531_4010_a48d_ad4d6b0818e8
-- name    : WilliamsonShmoys.planar_strict_supergraph_below_triangulation_bound_3909e30c_a531_4010_a48d_ad4d6b0818e8
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T13:29:40.766987+00:00
-- url     : https://prove2.me/theorems/279ea82e-1137-4707-afd7-6dd930290cf1
-- title:
--   Planar completion below the triangulation edge bound
-- statement:
--   If a drawable graph on at least three vertices has fewer than the triangulation edge bound, it has a strictly larger drawable supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_strict_supergraph_below_triangulation_bound_3909e30c_a531_4010_a48d_ad4d6b0818e8
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hsmall : J.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ K : SimpleGraph V,
      J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K ≠ J := by sorry
