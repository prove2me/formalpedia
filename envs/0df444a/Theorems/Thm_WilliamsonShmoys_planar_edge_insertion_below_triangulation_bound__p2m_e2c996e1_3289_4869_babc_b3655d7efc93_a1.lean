-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_insertion_below_triangulation_bound__p2m_e2c996e1_3289_4869_babc_b3655d7efc93_a1
-- name    : WilliamsonShmoys.planar_edge_insertion_below_triangulation_bound__p2m_e2c996e1_3289_4869_babc_b3655d7efc93_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:31:06.567982+00:00
-- url     : https://prove2.me/theorems/7a004575-a295-4f3c-8d74-3fb00efa8d41
-- title:
--   Edge insertion below the planar triangulation bound
-- statement:
--   A drawable simple graph on at least three vertices with fewer than 3|V|−6 edges has a strictly larger drawable simple supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_insertion_below_triangulation_bound__p2m_e2c996e1_3289_4869_babc_b3655d7efc93_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hSparse : H.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ K ≠ H := by sorry
