-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_addEdge_when_below_triangulation_count
-- name    : WilliamsonShmoys.planarDrawingOn_addEdge_when_below_triangulation_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:14:51.826515+00:00
-- url     : https://prove2.me/theorems/66209719-12f5-4dcd-8462-ea061cbcc224
-- title:
--   A sparse drawable graph has a drawable strict extension
-- statement:
--   If a drawable simple graph on at least three vertices has fewer than 3n−6 edges, some strict supergraph on the same vertices is also drawable.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_addEdge_when_below_triangulation_count
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hCard : 3 ≤ Fintype.card V)
    (hBelow : S.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ T : SimpleGraph V, S < T ∧ WilliamsonShmoys.HasPlanarDrawingOn T := by
  sorry
