-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulating_extension__p2m_dafc8434_c658_484f_b8e8_b76293ec5b82_a1
-- name    : WilliamsonShmoys.planar_graph_has_triangulating_extension__p2m_dafc8434_c658_484f_b8e8_b76293ec5b82_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:03:41.670363+00:00
-- url     : https://prove2.me/theorems/7b77c23b-62df-4ae5-b586-caedc2314578
-- title:
--   Planar graph extension to a triangulation
-- statement:
--   Every finite planar simple graph on at least three fixed vertices has a planar supergraph on the same vertex set with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_triangulating_extension__p2m_dafc8434_c658_484f_b8e8_b76293ec5b82_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
