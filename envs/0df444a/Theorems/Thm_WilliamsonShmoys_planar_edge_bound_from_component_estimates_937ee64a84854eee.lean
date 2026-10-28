-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_component_estimates_937ee64a84854eee
-- name    : WilliamsonShmoys.planar_edge_bound_from_component_estimates_937ee64a84854eee
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:34:24.773172+00:00
-- url     : https://prove2.me/theorems/856cfff3-0968-4f28-86fe-2c6aa57e559b
-- title:
--   Aggregate edge bounds over connected components
-- statement:
--   If every component with at least three vertices satisfies the connected planar edge estimate, then summing edge and vertex counts across the component partition yields the target. Singleton and two-vertex components are handled directly: singleton slack is zero, while a two-vertex component has at most one edge and slack at least two. If no component has at least three vertices, the two-edge hypothesis forces two edge-bearing two-vertex components, providing at least four units of slack. Prove by finite component counting and arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.planar_edge_bound_from_component_estimates_937ee64a84854eee
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hm : 2 ≤ L.edgeSet.ncard)
    (hlocal : ∀ (C : L.ConnectedComponent), ∀ [Fintype (↑C.supp)],
      3 ≤ Fintype.card (↑C.supp) →
        (L.induce C.supp).edgeSet.ncard + 6 ≤ 3 * Fintype.card (↑C.supp)) :
    L.edgeSet.ncard + 3 * Nat.card L.ConnectedComponent + 3 ≤
      3 * Fintype.card V := by sorry
