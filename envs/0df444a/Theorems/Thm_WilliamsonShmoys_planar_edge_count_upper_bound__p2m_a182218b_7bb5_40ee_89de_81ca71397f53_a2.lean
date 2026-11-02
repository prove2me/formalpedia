-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_a182218b_7bb5_40ee_89de_81ca71397f53_a2
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_a182218b_7bb5_40ee_89de_81ca71397f53_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:25:36.447222+00:00
-- url     : https://prove2.me/theorems/f0aba619-3680-404a-84c1-4b765821e2bd
-- title:
--   Upper bound on the edge count of a drawable graph
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has at most 3n − 6 edges. This isolates the Euler formula and edge-face incidence argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_a182218b_7bb5_40ee_89de_81ca71397f53_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
