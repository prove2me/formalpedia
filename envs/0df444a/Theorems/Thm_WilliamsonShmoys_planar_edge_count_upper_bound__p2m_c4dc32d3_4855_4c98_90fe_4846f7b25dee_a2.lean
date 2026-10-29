-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_c4dc32d3_4855_4c98_90fe_4846f7b25dee_a2
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c4dc32d3_4855_4c98_90fe_4846f7b25dee_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T21:12:20.852152+00:00
-- url     : https://prove2.me/theorems/c955d1e3-af39-465d-8618-7c677be66dad
-- title:
--   Planar drawing edge-count upper bound
-- statement:
--   For a graph with the given crossing-free drawing and at least three vertices, the edge count is at most 3n−6. This isolates the standard planar edge bound. A proof route is to obtain a planar embedding from the arc witness, apply Euler's formula componentwise or after connecting components, and bound face boundary lengths. The parent uses this bound directly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c4dc32d3_4855_4c98_90fe_4846f7b25dee_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
