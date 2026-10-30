-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_upper_bound_completion_55e40668_6c6c_445f_853d_a7074df51c4e
-- name    : WilliamsonShmoys.planar_simple_edge_upper_bound_completion_55e40668_6c6c_445f_853d_a7074df51c4e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:32:11.931594+00:00
-- url     : https://prove2.me/theorems/1bfd1ab4-3ecd-4143-b631-a1ca37f2bbdf
-- title:
--   Simple planar graph edge upper bound
-- statement:
--   A simply drawn planar graph on at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_edge_upper_bound_completion_55e40668_6c6c_445f_853d_a7074df51c4e
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
