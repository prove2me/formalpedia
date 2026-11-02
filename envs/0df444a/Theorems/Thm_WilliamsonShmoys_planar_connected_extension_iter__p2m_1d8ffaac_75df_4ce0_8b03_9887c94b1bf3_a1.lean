-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_extension_iter__p2m_1d8ffaac_75df_4ce0_8b03_9887c94b1bf3_a1
-- name    : WilliamsonShmoys_planar_connected_extension_iter__p2m_1d8ffaac_75df_4ce0_8b03_9887c94b1bf3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:59:14.340762+00:00
-- url     : https://prove2.me/theorems/b2e13e2c-7940-49b0-8981-b81202d974e6
-- title:
--   Iterate planar component-joining steps
-- statement:
--   For a finite vertex type, if every disconnected planar supergraph encountered above the starting graph admits a planar extension with an edge joining two previously unreachable vertices, then some planar supergraph of the starting graph is connected. Prove this by finite induction on connected components: each step merges at least two components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys_planar_connected_extension_iter__p2m_1d8ffaac_75df_4ce0_8b03_9887c94b1bf3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hstep : ∀ (K : SimpleGraph V), H ≤ K → HasPlanarDrawingOn K → ¬ K.Connected →
      ∃ L : SimpleGraph V, ∃ u v : V,
        K ≤ L ∧ HasPlanarDrawingOn L ∧ ¬ K.Reachable u v ∧ L.Adj u v) :
    ∃ G : SimpleGraph V, H ≤ G ∧ HasPlanarDrawingOn G ∧ G.Connected := by sorry
