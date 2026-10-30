-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_count_upper_disconnected
-- name    : WilliamsonShmoys.planar_drawable_edge_count_upper_disconnected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:59:06.233159+00:00
-- url     : https://prove2.me/theorems/750f83fd-53ba-456e-9338-6f04ee193e86
-- title:
--   Upper edge bound for a disconnected drawable graph
-- statement:
--   A disconnected finite simple graph with at least three vertices and a crossing-free drawing has at most 3|V| − 6 edges. Restrict the drawing to its connected components; prove the Euler bound for components of size at least three, bound the smaller components directly, then sum the component estimates. The total-size hypothesis is needed to recover the additive six in the final bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_edge_count_upper_disconnected
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hdisc : ¬ K.Connected) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
