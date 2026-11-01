-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_fixed_bridge__p2m_9ff46b9a_d59b_4c3c_9ec1_099be280d4ab_a1
-- name    : WilliamsonShmoys.planar_drawing_add_fixed_bridge__p2m_9ff46b9a_d59b_4c3c_9ec1_099be280d4ab_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:07:57.412663+00:00
-- url     : https://prove2.me/theorems/016bc9c9-be0e-41b2-afe4-acfa54df6433
-- title:
--   Add a bridge between a fixed unreachable pair in a planar drawing
-- statement:
--   For any two vertices in different connected components of a finite ordered graph with a crossing-free drawing, there is a supergraph on the same vertices that retains a crossing-free drawing and includes an edge between those vertices. Unreachability ensures the endpoints are distinct.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_fixed_bridge__p2m_9ff46b9a_d59b_4c3c_9ec1_099be280d4ab_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    {u v : V}
    (hUnreachable : ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ HasPlanarDrawingOn K ∧ K.Adj u v := by sorry
