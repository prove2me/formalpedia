-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_ac994e54_6c64_49c2_8ec9_d8877c55139c_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_ac994e54_6c64_49c2_8ec9_d8877c55139c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T02:37:09.710796+00:00
-- url     : https://prove2.me/theorems/d26c9022-2329-43dc-a71b-93dff737cb2c
-- title:
--   Planar simple graphs have at most 3n minus 6 edges
-- statement:
--   Any simple graph with at least three vertices and a drawing satisfying `HasPlanarDrawingOn` has at most 3n−6 edges. This is the Euler-formula and face-incidence upper bound; for a disconnected drawing, connect its components by noncrossing arcs before applying the connected bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_ac994e54_6c64_49c2_8ec9_d8877c55139c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
