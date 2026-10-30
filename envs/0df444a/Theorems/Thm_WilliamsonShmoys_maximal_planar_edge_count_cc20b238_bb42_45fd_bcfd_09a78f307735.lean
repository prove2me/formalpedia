-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_cc20b238_bb42_45fd_bcfd_09a78f307735
-- name    : WilliamsonShmoys.maximal_planar_edge_count_cc20b238_bb42_45fd_bcfd_09a78f307735
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:07:20.463787+00:00
-- url     : https://prove2.me/theorems/4cd7eb3f-e59a-457a-b380-50eca75bdcdd
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A finite drawable simple graph on at least three vertices that is maximal among drawable graphs on the same vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_cc20b238_bb42_45fd_bcfd_09a78f307735
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      (∀ u v, K.Adj u v → L.Adj u v) →
      HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
