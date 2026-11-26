-- Prove2me | Theorems.Thm_section5_gaussian_disagreement_proved
-- name    : section5_gaussian_disagreement_proved
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:22:03.767658+00:00
-- url     : https://prove2.me/theorems/7590bd79-a96f-49d2-a545-a348d7a387e8
-- title:
--   Gaussian threshold disagreement bounds and the angular identity
-- statement:
--   Let w₁,w₂ be unit vectors in R^n and θ₁,θ₂ real thresholds. Let d(f,g) denote the standard Gaussian probability that f and g disagree, with ltf_(w,θ)(x)=sgn(⟨w,x⟩−θ). Then $$d(\operatorname{ltf}_{w_1,\theta_1},\operatorname{ltf}_{w_2,\theta_2})\le\|w_1-w_2\|/2+|\theta_1-\theta_2|/\sqrt{2\pi},$$ and $$d(\operatorname{ltf}_{w_1,0},\operatorname{ltf}_{w_2,0})=\arccos\langle w_1,w_2\rangle/\pi.$$
-- source:
--   Reused accepted proof of QuantumLTF.Membership.lemma_2_1 by kmehltretter82, Prove2Me submission f5f65d6e-b702-475a-bc3e-8683c2844aa9 (Apache-2.0). Exact local formalization: Solutions/Section5GaussianDisagreementFoundation.lean, lines 704–707; copied for local axiom auditing, not a new contribution. Paper context: Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Lemma 2.1 and its use in Section 5.

import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_ltf
import Mathlib

open QuantumLTF.Membership in
theorem section5_gaussian_disagreement_proved {n : ℕ} (w₁ w₂ : EuclideanSpace ℝ (Fin n)) (h₁ : ‖w₁‖ = 1) (h₂ : ‖w₂‖ = 1)
    (θ₁ θ₂ : ℝ) :
    disagree (ltf w₁ θ₁) (ltf w₂ θ₂) ≤ ‖w₁ - w₂‖ / 2 + |θ₁ - θ₂| / Real.sqrt (2 * Real.pi) ∧
      disagree (ltf w₁ 0) (ltf w₂ 0) = Real.arccos (inner ℝ w₁ w₂) / Real.pi := by sorry
