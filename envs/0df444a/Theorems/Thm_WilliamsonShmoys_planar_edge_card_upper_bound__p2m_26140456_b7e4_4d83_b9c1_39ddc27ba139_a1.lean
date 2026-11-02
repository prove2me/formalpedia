-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_card_upper_bound__p2m_26140456_b7e4_4d83_b9c1_39ddc27ba139_a1
-- name    : WilliamsonShmoys.planar_edge_card_upper_bound__p2m_26140456_b7e4_4d83_b9c1_39ddc27ba139_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:51:56.270203+00:00
-- url     : https://prove2.me/theorems/55bcde83-43a5-4c62-ba9b-1744a34b8f86
-- title:
--   Planar graph edge upper bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3|V| − 6 edges. This removes the general planar upper-bound argument from the parent; prove it by establishing Euler’s formula for the drawing and counting at least three edge-sides around each face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_card_upper_bound__p2m_26140456_b7e4_4d83_b9c1_39ddc27ba139_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
