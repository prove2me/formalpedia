-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_bound
-- name    : WilliamsonShmoys.planar_drawable_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T05:44:24.664522+00:00
-- url     : https://prove2.me/theorems/393079c8-2287-4f16-aabd-1d5c2a32811b
-- title:
--   Planar drawable graphs satisfy the simple planar edge bound
-- statement:
--   Every finite drawable simple graph on at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hV : 3 <= Fintype.card V) :
    R.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
