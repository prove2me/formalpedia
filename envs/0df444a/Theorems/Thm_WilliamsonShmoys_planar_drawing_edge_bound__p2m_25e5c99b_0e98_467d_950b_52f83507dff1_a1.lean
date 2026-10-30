-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_25e5c99b_0e98_467d_950b_52f83507dff1_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_25e5c99b_0e98_467d_950b_52f83507dff1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:33:35.069569+00:00
-- url     : https://prove2.me/theorems/3a2545dd-3002-4f8f-92b3-b56d526d92af
-- title:
--   Edge bound for a drawable finite simple graph
-- statement:
--   Every drawable finite simple graph with at least three vertices has at most 3|V|−6 edges, including when it is disconnected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_25e5c99b_0e98_467d_950b_52f83507dff1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  sorry
