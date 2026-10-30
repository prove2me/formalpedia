-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_retry_49abde41
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_retry_49abde41
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T05:24:11.949204+00:00
-- url     : https://prove2.me/theorems/eb93e679-8821-41f1-b787-569e84785022
-- title:
--   Planar simple graphs have at most 3n − 6 edges
-- statement:
--   Every finite simple graph with this crossing-free drawing and at least three vertices has at most `3|V|−6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_retry_49abde41
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    (H.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by sorry
