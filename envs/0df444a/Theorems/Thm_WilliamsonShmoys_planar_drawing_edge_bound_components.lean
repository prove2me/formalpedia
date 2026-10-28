-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_components
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_components
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T22:37:07.692786+00:00
-- url     : https://prove2.me/theorems/005e7c09-83c5-46b4-ac25-59a30d5c2383
-- title:
--   Component-sensitive planar edge bound
-- statement:
--   A simple graph with a crossing-free drawing, at least three vertices, and at least two edges satisfies the component-sensitive planar edge bound when c is the component count. This removes the topological and component-counting work from the parent; the parent combines it with Euler’s equation by linear arithmetic. A proof can decompose into connected components, use the simple planar edge bound on components with at least three vertices, and separately bound components of size one or two, then aggregate using the global size and edge hypotheses. The remaining core obligation is establishing this edge bound from the exact supplied drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound_components
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hm : 2 ≤ L.edgeSet.ncard)
    (c : ℕ) :
    L.edgeSet.ncard + 3 * c + 3 ≤ 3 * Fintype.card V := by sorry
