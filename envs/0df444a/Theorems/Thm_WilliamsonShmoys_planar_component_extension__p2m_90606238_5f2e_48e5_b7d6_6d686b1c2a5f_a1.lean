-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_component_extension__p2m_90606238_5f2e_48e5_b7d6_6d686b1c2a5f_a1
-- name    : WilliamsonShmoys.planar_component_extension__p2m_90606238_5f2e_48e5_b7d6_6d686b1c2a5f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:07:50.330189+00:00
-- url     : https://prove2.me/theorems/0ac1f81c-3fb8-44a1-92c7-855048ff841d
-- title:
--   Connect the components of a plane graph by added edges
-- statement:
--   A finite disconnected drawn graph has a connected drawn supergraph whose added edges each join vertices from different original connected components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_component_extension__p2m_90606238_5f2e_48e5_b7d6_6d686b1c2a5f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hNotConnected : ¬ K.Connected) :
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧ K ≤ H ∧ H.Connected ∧
      ∀ x y : V, H.Adj x y → K.Adj x y ∨ ¬ K.Reachable x y := by sorry
