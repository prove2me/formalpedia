-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count_57da26e6_40fa_4eeb_a0ea_166241e54306
-- name    : WilliamsonShmoys.planar_completion_edge_count_57da26e6_40fa_4eeb_a0ea_166241e54306
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T12:51:39.675996+00:00
-- url     : https://prove2.me/theorems/1794ae85-4ddf-4fc1-b226-9d54b8be81b3
-- title:
--   Planar drawing completion with the maximal edge count
-- statement:
--   Every finite simple graph on at least three vertices with a crossing-free drawing has a drawable supergraph on the same vertex set with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_edge_count_57da26e6_40fa_4eeb_a0ea_166241e54306
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
