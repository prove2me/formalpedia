-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_planar_edge_upper_bound
-- name    : WilliamsonShmoys.maximal_drawable_graph_planar_edge_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:47:37.961722+00:00
-- url     : https://prove2.me/theorems/3daf7e3a-ae1d-432d-a891-6f4c577cf93d
-- title:
--   Planar simple graphs satisfy the Euler edge upper bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3n−6 edges. This is the Euler face-count upper bound, including disconnected graphs and small components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_planar_edge_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hPdraw : HasPlanarDrawingOn P)
    (hCard : 3 ≤ Fintype.card V) :
    P.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
