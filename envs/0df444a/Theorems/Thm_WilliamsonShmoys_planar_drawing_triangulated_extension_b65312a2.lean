-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_extension_b65312a2
-- name    : WilliamsonShmoys.planar_drawing_triangulated_extension_b65312a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:24:22.942718+00:00
-- url     : https://prove2.me/theorems/79b254f3-bdb8-4d00-a5c1-60f5c6baa20f
-- title:
--   Triangulated drawable extension
-- statement:
--   Every finite drawable simple graph on at least three vertices extends, on the same vertex set, to a drawable graph with exactly 3n−6 edges. This is the triangulation step used by the parent; maximality then forces the extension to equal the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulated_extension_b65312a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hMdraw : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      3 * Fintype.card V = N.edgeSet.ncard + 6 := by sorry
