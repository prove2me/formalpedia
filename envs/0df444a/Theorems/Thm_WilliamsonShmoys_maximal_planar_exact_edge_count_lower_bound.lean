-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_exact_edge_count_lower_bound
-- name    : WilliamsonShmoys.maximal_planar_exact_edge_count_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T05:01:12.350423+00:00
-- url     : https://prove2.me/theorems/914e39cc-31b6-4e99-94ff-c1d958ad362c
-- title:
--   Maximal drawable graphs attain the planar edge bound
-- statement:
--   A drawable finite simple graph with at least three vertices that is maximal among drawable supergraphs on the same vertex type has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_exact_edge_count_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
