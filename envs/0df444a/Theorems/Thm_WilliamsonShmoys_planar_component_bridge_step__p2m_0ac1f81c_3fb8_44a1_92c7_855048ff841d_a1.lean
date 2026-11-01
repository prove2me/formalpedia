-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_component_bridge_step__p2m_0ac1f81c_3fb8_44a1_92c7_855048ff841d_a1
-- name    : WilliamsonShmoys.planar_component_bridge_step__p2m_0ac1f81c_3fb8_44a1_92c7_855048ff841d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:24:09.939918+00:00
-- url     : https://prove2.me/theorems/acec796e-6702-4a6d-b606-681b7456e1fa
-- title:
--   Add one planar bridge between components
-- statement:
--   Extend a disconnected planar supergraph of K by a new planar edge whose endpoints belong to different original K components, preserving the condition on every added edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_component_bridge_step__p2m_0ac1f81c_3fb8_44a1_92c7_855048ff841d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K G : SimpleGraph V)
    (hKG : K ≤ G)
    (hInvariant : ∀ x y : V, G.Adj x y → K.Adj x y ∨ ¬ K.Reachable x y)
    (hG : HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧ G ≤ H ∧
      (∀ x y : V, H.Adj x y → G.Adj x y ∨ ¬ K.Reachable x y) ∧
      ∃ u v : V, ¬ G.Adj u v ∧ H.Adj u v := by sorry
