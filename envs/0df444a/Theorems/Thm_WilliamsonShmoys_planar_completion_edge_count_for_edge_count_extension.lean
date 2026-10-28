-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count_for_edge_count_extension
-- name    : WilliamsonShmoys.planar_completion_edge_count_for_edge_count_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:50:43.052082+00:00
-- url     : https://prove2.me/theorems/06465f73-9c5b-45b1-98af-f24d50b6286d
-- title:
--   Planar completion with the maximal planar edge count
-- statement:
--   Every graph with a crossing-free drawing on a finite linearly ordered vertex type of size at least three has a planar supergraph on the same vertex type with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_edge_count_for_edge_count_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      HasPlanarDrawingOn K ∧
      J.edgeSet ⊆ K.edgeSet ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
