-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_edge_count
-- name    : WilliamsonShmoys.exists_drawable_supergraph_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:26:07.912667+00:00
-- url     : https://prove2.me/theorems/ceefaedf-5be0-45d9-8d5f-26f80fa1b1eb
-- title:
--   Drawable supergraph attaining the planar edge bound
-- statement:
--   Every finite simple graph on at least three vertices with a crossing-free drawing has a drawable supergraph on the same vertices with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_drawable_supergraph_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V - 6 = M.edgeSet.ncard := by
  sorry
