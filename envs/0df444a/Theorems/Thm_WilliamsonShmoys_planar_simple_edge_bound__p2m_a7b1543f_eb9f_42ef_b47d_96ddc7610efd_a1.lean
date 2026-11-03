-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound__p2m_a7b1543f_eb9f_42ef_b47d_96ddc7610efd_a1
-- name    : WilliamsonShmoys.planar_simple_edge_bound__p2m_a7b1543f_eb9f_42ef_b47d_96ddc7610efd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:06:13.778725+00:00
-- url     : https://prove2.me/theorems/1bf322db-0dbd-4aed-abd6-bf402bf7bb2f
-- title:
--   Simple planar graph edge upper bound
-- statement:
--   A finite simple graph with a drawing satisfying HasPlanarDrawingOn and at least three vertices has at most 3|V|-6 edges. This is the planar upper bound and does not assume maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_edge_bound__p2m_a7b1543f_eb9f_42ef_b47d_96ddc7610efd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
