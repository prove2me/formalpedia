-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_3a2fa668_af0b_4223_89b0_dcabec19097b_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_3a2fa668_af0b_4223_89b0_dcabec19097b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:30:52.382791+00:00
-- url     : https://prove2.me/theorems/8f2b622d-d69e-48f3-b5b2-9dea858b8d8f
-- title:
--   Planar edge count upper bound
-- statement:
--   Any simple graph with a drawing satisfying HasPlanarDrawingOn, on at least three finite linearly ordered vertices, has at most three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_3a2fa668_af0b_4223_89b0_dcabec19097b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
