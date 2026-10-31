-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_upper_bound__p2m_2094dec4_72bc_4506_8cb1_28494e96e3ad_a1
-- name    : WilliamsonShmoys_planar_simple_edge_upper_bound__p2m_2094dec4_72bc_4506_8cb1_28494e96e3ad_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:21:57.507971+00:00
-- url     : https://prove2.me/theorems/0cbdf370-052c-4f7e-80db-29586f4df68b
-- title:
--   Euler upper bound for a finite simple planar graph
-- statement:
--   This is the reusable planar edge upper bound. It removes the upper-bound half of the target; a proof route is Euler’s formula for the drawing together with the fact that each face of a simple planar graph with at least three vertices has boundary length at least three. The finite vertex bound handles the small-graph boundary cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys_planar_simple_edge_upper_bound__p2m_2094dec4_72bc_4506_8cb1_28494e96e3ad_a1
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
