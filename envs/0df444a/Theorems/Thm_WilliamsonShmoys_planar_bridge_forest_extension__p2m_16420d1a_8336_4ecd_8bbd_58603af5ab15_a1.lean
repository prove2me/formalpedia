-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_bridge_forest_extension__p2m_16420d1a_8336_4ecd_8bbd_58603af5ab15_a1
-- name    : WilliamsonShmoys.planar_bridge_forest_extension__p2m_16420d1a_8336_4ecd_8bbd_58603af5ab15_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:38:37.469928+00:00
-- url     : https://prove2.me/theorems/276aaf4b-f543-4b59-a5b3-dd180aa8d736
-- title:
--   Adding a component-joining star preserves planarity
-- statement:
--   If a finite graph H has a planar drawing and F consists of edges incident to one optional center, with every F edge joining distinct H components, then connectedness of H ⊔ F lets us draw H ⊔ F planarly. With no center, F has no edges, covering the empty vertex type when connectedness is vacuous.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_bridge_forest_extension__p2m_16420d1a_8336_4ecd_8bbd_58603af5ab15_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H F : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel F.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hStar : ∃ c : Option V, ∀ ⦃u v : V⦄, F.Adj u v → c = some u ∨ c = some v)
    (hAcross : ∀ ⦃u v : V⦄, F.Adj u v → ¬ H.Reachable u v)
    (hConnected : (H ⊔ F).Connected) :
    WilliamsonShmoys.HasPlanarDrawingOn (H ⊔ F) := by
  sorry
