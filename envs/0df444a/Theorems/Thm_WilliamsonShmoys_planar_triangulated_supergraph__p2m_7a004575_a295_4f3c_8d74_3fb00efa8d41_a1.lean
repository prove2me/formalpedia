-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulated_supergraph__p2m_7a004575_a295_4f3c_8d74_3fb00efa8d41_a1
-- name    : WilliamsonShmoys.planar_triangulated_supergraph__p2m_7a004575_a295_4f3c_8d74_3fb00efa8d41_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:40:51.997276+00:00
-- url     : https://prove2.me/theorems/ef9c63a2-b89d-412e-ad8e-f938ea808c23
-- title:
--   Planar triangulation supergraph
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set whose number of edges is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulated_supergraph__p2m_7a004575_a295_4f3c_8d74_3fb00efa8d41_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
