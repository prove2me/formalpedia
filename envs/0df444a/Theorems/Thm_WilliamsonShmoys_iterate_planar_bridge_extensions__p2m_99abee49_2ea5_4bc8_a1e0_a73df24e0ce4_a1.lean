-- Prove2me | Theorems.Thm_WilliamsonShmoys_iterate_planar_bridge_extensions__p2m_99abee49_2ea5_4bc8_a1e0_a73df24e0ce4_a1
-- name    : WilliamsonShmoys.iterate_planar_bridge_extensions__p2m_99abee49_2ea5_4bc8_a1e0_a73df24e0ce4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:56:24.146434+00:00
-- url     : https://prove2.me/theorems/596e37ff-bf61-48b7-90c3-a4814329de9c
-- title:
--   Iterate planar bridge extensions to connect a graph
-- statement:
--   If every planar graph on a finite vertex type admits a planar extension by an edge between any two unreachable vertices, then it admits a connected planar supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.iterate_planar_bridge_extensions__p2m_99abee49_2ea5_4bc8_a1e0_a73df24e0ce4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hstep : ∀ (G : SimpleGraph V), (dG : DecidableRel G.Adj) →
      WilliamsonShmoys.HasPlanarDrawingOn G →
      ∀ u v, ¬ G.Reachable u v →
        ∃ H : SimpleGraph V,
          (∀ a b, H.Adj a b ↔
            G.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ∧
          WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  sorry
