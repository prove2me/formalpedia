-- Prove2me | Theorems.Thm_p2m_sum_complementarity
-- name    : p2m_sum_complementarity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T16:07:02.282543+00:00
-- url     : https://prove2.me/theorems/db120e34-3d51-4cd7-a296-4387db159083
-- title:
--   p2m_sum_complementarity
-- statement:
--   Automatically extracted helper theorem p2m_sum_complementarity from oversized parent candidate b2ac6b5b12de4b1e5c6bc3515e11c7a1be67296ceda1c51e95842872d3844a7d.
-- source:
--   candidate-decomposition:5c19a469-c8c3-4610-9c11-ae7734488256:b2ac6b5b12de4b1e5c6bc3515e11c7a1be67296ceda1c51e95842872d3844a7d

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing

theorem p2m_sum_complementarity {k : ℕ} (x z dx dz : Fin k → ℝ) (μ : ℝ)
    (hcomp : ∀ i, z i * dx i + x i * dz i = μ - x i * z i) :
    (∑ i : Fin k, (z i * dx i + x i * dz i)) =
      (k : ℝ) * μ - z ⬝ᵥ x := by sorry
