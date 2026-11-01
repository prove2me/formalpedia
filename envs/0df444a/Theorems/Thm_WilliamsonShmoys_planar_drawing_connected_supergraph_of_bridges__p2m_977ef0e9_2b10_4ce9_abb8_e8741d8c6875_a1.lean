-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_of_bridges__p2m_977ef0e9_2b10_4ce9_abb8_e8741d8c6875_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph_of_bridges__p2m_977ef0e9_2b10_4ce9_abb8_e8741d8c6875_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:50:39.442807+00:00
-- url     : https://prove2.me/theorems/99abee49-2ea5-4bc8-a1e0-a73df24e0ce4
-- title:
--   Iterate planar bridge extensions to connect a graph
-- statement:
--   Assuming any planar drawing can be extended by an edge between vertices in different components, finitely many such extensions produce a connected planar supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_supergraph_of_bridges__p2m_977ef0e9_2b10_4ce9_abb8_e8741d8c6875_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hbridge : ∀ (G : SimpleGraph V), (dG : DecidableRel G.Adj) →
      WilliamsonShmoys.HasPlanarDrawingOn G →
      ∀ u v, ¬ G.Reachable u v →
        ∃ H : SimpleGraph V,
          (∀ a b, H.Adj a b ↔
            G.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ∧
          WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  sorry
