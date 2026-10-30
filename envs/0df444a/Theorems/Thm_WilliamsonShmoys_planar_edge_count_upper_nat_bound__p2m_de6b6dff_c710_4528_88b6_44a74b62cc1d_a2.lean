-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_nat_bound__p2m_de6b6dff_c710_4528_88b6_44a74b62cc1d_a2
-- name    : WilliamsonShmoys.planar_edge_count_upper_nat_bound__p2m_de6b6dff_c710_4528_88b6_44a74b62cc1d_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T02:55:33.582717+00:00
-- url     : https://prove2.me/theorems/3a451d60-87da-4886-886e-4eafc63f3bd5
-- title:
--   Planar edge count upper bound
-- statement:
--   Any finite simple graph with the specified crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This is the classical planar Euler upper bound, useful independently of maximality; prove it by reducing to connected components and applying Euler’s formula with the face-boundary count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_nat_bound__p2m_de6b6dff_c710_4528_88b6_44a74b62cc1d_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
