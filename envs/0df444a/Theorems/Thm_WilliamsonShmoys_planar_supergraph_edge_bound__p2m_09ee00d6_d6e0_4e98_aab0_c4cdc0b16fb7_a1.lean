-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_bound__p2m_09ee00d6_d6e0_4e98_aab0_c4cdc0b16fb7_a1
-- name    : WilliamsonShmoys.planar_supergraph_edge_bound__p2m_09ee00d6_d6e0_4e98_aab0_c4cdc0b16fb7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:35:42.223265+00:00
-- url     : https://prove2.me/theorems/16f13def-1905-44d4-887c-a7f874e9f4a3
-- title:
--   Dense drawable supergraph augmentation
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_edge_bound__p2m_09ee00d6_d6e0_4e98_aab0_c4cdc0b16fb7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdraw : HasPlanarDrawingOn L) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    ∃ M : SimpleGraph V,
      L.edgeFinset ⊆ M.edgeFinset ∧
      HasPlanarDrawingOn M ∧
      3 * Fintype.card V - 6 ≤ M.edgeFinset.card := by
  sorry
