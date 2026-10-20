-- Prove2me | Theorems.Thm_p2m_path_geometric_recurrence_upto
-- name    : p2m_path_geometric_recurrence_upto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T16:27:12.906729+00:00
-- url     : https://prove2.me/theorems/1a57c0e3-584e-4584-8d14-d66cb1ac8bf4
-- title:
--   p2m_path_geometric_recurrence_upto
-- statement:
--   Automatically extracted helper theorem p2m_path_geometric_recurrence_upto from oversized parent candidate deeb0988f6eb99b823165bfae6db19d2790d451a1af46fa48f3bd2b5b8fd3c45.
-- source:
--   candidate-decomposition:220d8944-f802-44d2-966d-fe70c0b837f8:deeb0988f6eb99b823165bfae6db19d2790d451a1af46fa48f3bd2b5b8fd3c45

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing

section
theorem p2m_path_geometric_recurrence_upto {δ t M R : ℝ} (K : ℕ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hM : 0 ≤ M) (hR : 0 ≤ R) (γ : ℕ → ℝ)
    (hrec : ∀ k, k + 1 ≤ K →
      γ (k + 1) ≤ (1 - t * (1 - δ)) * γ k + M * (1 - t) ^ k * R) :
    ∀ k ≤ K, γ k ≤ (1 - t * (1 - δ)) ^ k * (γ 0 + M * R / (δ * t)) := by sorry
end
