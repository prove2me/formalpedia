-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_53dddbcd_67dc_454e_b4d2_26f3b045c421
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_53dddbcd_67dc_454e_b4d2_26f3b045c421
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T02:44:11.640088+00:00
-- url     : https://prove2.me/theorems/1bec9fe1-f96d-4d95-8b96-08ac82faf267
-- title:
--   Euler upper bound for a simple planar graph
-- statement:
--   A simple graph with the supplied crossing-free drawing and at least three vertices has at most 3|V| − 6 edges. The proof uses Euler’s formula; disconnected components can be joined in the complement before applying the connected planar bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_53dddbcd_67dc_454e_b4d2_26f3b045c421
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    (M.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by sorry
