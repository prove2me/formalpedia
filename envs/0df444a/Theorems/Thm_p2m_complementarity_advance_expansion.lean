-- Prove2me | Theorems.Thm_p2m_complementarity_advance_expansion
-- name    : p2m_complementarity_advance_expansion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T16:43:15.302984+00:00
-- url     : https://prove2.me/theorems/7af33f1c-4c13-4fbe-a19c-c25e6988dca2
-- title:
--   p2m_complementarity_advance_expansion
-- statement:
--   Automatically extracted helper theorem p2m_complementarity_advance_expansion from oversized parent candidate b9482e2d82ed9470f262081c9326914da918d3f9ba39cfa65016338f19db74f6.
-- source:
--   candidate-decomposition:5c19a469-c8c3-4610-9c11-ae7734488256:b9482e2d82ed9470f262081c9326914da918d3f9ba39cfa65016338f19db74f6

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
import Theorems.Thm_p2m_sum_complementarity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing

theorem p2m_complementarity_advance_expansion {m n : ℕ}
    (p d : PDPoint m n) (θ : ℝ) :
    complementarity (p.advance θ d) = complementarity p +
      θ * ((∑ j : Fin n, (p.z j * d.x j + p.x j * d.z j)) +
        (∑ i : Fin m, (p.w i * d.y i + p.y i * d.w i))) +
      θ ^ 2 * (d.z ⬝ᵥ d.x + d.y ⬝ᵥ d.w) := by sorry
