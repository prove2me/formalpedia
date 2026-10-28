-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_c7a07234_8856_4e73_ae2f_62c3fa66bc64_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c7a07234_8856_4e73_ae2f_62c3fa66bc64_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:39:55.45143+00:00
-- url     : https://prove2.me/theorems/73b3577f-2c71-4c0f-80a1-6f6ab444c366
-- title:
--   Euler upper bound for planar simple graphs
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3|V|−6 edges. This is the Euler upper bound and remains valid for disconnected planar graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c7a07234_8856_4e73_ae2f_62c3fa66bc64_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    N.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
