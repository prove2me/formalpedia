-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_exact_maximal_edge_count__p2m_b086cf8e_feab_4218_a571_b7d2828fd0cf_a1
-- name    : WilliamsonShmoys.planar_supergraph_with_exact_maximal_edge_count__p2m_b086cf8e_feab_4218_a571_b7d2828fd0cf_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:55:20.907537+00:00
-- url     : https://prove2.me/theorems/5b34d21f-5de2-4900-bb56-08556ec4330c
-- title:
--   Planar augmentation to the triangulation edge count
-- statement:
--   Any planar graph on a finite ordered vertex type with at least three vertices has a planar supergraph on the same vertices with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_with_exact_maximal_edge_count__p2m_b086cf8e_feab_4218_a571_b7d2828fd0cf_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, (∀ {u v : V}, K.Adj u v → L.Adj u v) ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
