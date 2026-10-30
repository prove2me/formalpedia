-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_36583a35
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_36583a35
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:42:41.184985+00:00
-- url     : https://prove2.me/theorems/241a66e7-9a3c-4b00-9505-d674adbb2282
-- title:
--   Planar edge count upper bound for this completion theorem
-- statement:
--   A finite drawable simple graph on at least three vertices has at most 3|V|−6 edges, whether or not it is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_36583a35
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    (K.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 := by sorry
