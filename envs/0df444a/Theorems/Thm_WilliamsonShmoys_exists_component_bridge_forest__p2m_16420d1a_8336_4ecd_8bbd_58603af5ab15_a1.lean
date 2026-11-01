-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_component_bridge_forest__p2m_16420d1a_8336_4ecd_8bbd_58603af5ab15_a1
-- name    : WilliamsonShmoys.exists_component_bridge_forest__p2m_16420d1a_8336_4ecd_8bbd_58603af5ab15_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-31T21:38:39.457297+00:00
-- url     : https://prove2.me/theorems/54b43118-f594-4f77-a818-8a20b75837d9
-- title:
--   Choose a star connecting the graph components
-- statement:
--   For a finite graph H, choose a star F whose edges join different connected components so that H ⊔ F is connected. If V is empty, take F edgeless and the optional center absent; otherwise choose one root component and join a representative of every other component to a vertex in that root component.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_component_bridge_forest__p2m_16420d1a_8336_4ecd_8bbd_58603af5ab15_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∃ F : SimpleGraph V,
      (∃ c : Option V, ∀ ⦃u v : V⦄, F.Adj u v → c = some u ∨ c = some v) ∧
      (∀ ⦃u v : V⦄, F.Adj u v → ¬ H.Reachable u v) ∧
      (H ⊔ F).Connected := by
  sorry
