-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_upper_bound__p2m_53911c92_d38e_4043_bb6e_65b3932704cd_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound__p2m_53911c92_d38e_4043_bb6e_65b3932704cd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:31:40.049954+00:00
-- url     : https://prove2.me/theorems/3d77748d-afb6-44ab-af6e-074dde905918
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   A simple graph with a crossing-free drawing and at least three vertices has at most $3|V|-6$ edges. This is the Euler-formula upper bound; the lower bound on the vertex count is needed for the stated form.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound__p2m_53911c92_d38e_4043_bb6e_65b3932704cd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
