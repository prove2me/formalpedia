-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_18bbe9c1_8b0d_4062_b19f_3ec33678fcd4_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_18bbe9c1_8b0d_4062_b19f_3ec33678fcd4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:06:51.225394+00:00
-- url     : https://prove2.me/theorems/1c06af72-8ad5-473e-9376-40ba591256d7
-- title:
--   Planar simple graphs have at most 3n−6 edges
-- statement:
--   A simple graph with a crossing-free drawing and at least three vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_18bbe9c1_8b0d_4062_b19f_3ec33678fcd4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdrawing : HasPlanarDrawingOn G) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
