-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_upper_bound__p2m_7e36ab91_a082_401a_9ddf_0fa0bcba787f_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_7e36ab91_a082_401a_9ddf_0fa0bcba787f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:27:02.535694+00:00
-- url     : https://prove2.me/theorems/6fae641e-69bd-437f-8912-51466427af04
-- title:
--   Euler upper bound for a planar graph
-- statement:
--   Every finite simple graph with at least three vertices admitting the supplied planar drawing has at most 3|V|−6 edges. This is the Euler upper-bound half of the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_7e36ab91_a082_401a_9ddf_0fa0bcba787f_a1
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
