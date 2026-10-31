-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_4d9bb183_475b_4a59_8b75_1a8cda8dae1d_a2
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_4d9bb183_475b_4a59_8b75_1a8cda8dae1d_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:38:18.383213+00:00
-- url     : https://prove2.me/theorems/6fab6ec6-c4a2-4215-b61d-4e14bbc8fe70
-- title:
--   Upper edge bound for simple planar graphs
-- statement:
--   A finite simple graph on at least three vertices with a crossing-free drawing has at most 3|V|−6 edges, by the planar Euler edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_4d9bb183_475b_4a59_8b75_1a8cda8dae1d_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel L.Adj := dL
    L.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
