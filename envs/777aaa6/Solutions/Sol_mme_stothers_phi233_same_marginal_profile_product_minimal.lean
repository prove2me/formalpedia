-- Prove2me | solution 1 for mme_stothers_phi233_same_marginal_profile_product_minimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:27:16.561257+00:00
-- url     : https://prove2.me/submissions/0aefab02-8c6a-48d3-af27-1b8f46a8c807

import Theorems.Thm_mme_phi233_profile_product_mono_of_entropy_cost_le
import Theorems.Thm_mme_stothers_phi233_same_marginal_entropy_minimal

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (E H L : ℝ) (hE : 0 < E) (hH : 0 < H)
    (hEL : E < L) (hHL : H < L) :
    let sigma := 2 * H / (2 * H + L)
    let mu := E / (E + L)
    ∃ a b c d : ℝ,
      0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧
      2 * a + b + c + d = 1 ∧
      2 * a + b = sigma ∧ a + c = mu ∧
      ∀ a' b' c' d' : ℝ,
        0 ≤ a' → 0 ≤ b' → 0 ≤ c' → 0 ≤ d' →
        2 * a' + b' + c' + d' = 1 →
        2 * a' + b' = sigma → a' + c' = mu →
        a ^ (2 * a) * b ^ b * c ^ c * d ^ d ≤
          a' ^ (2 * a') * b' ^ b' * c' ^ c' * d' ^ d' := by
  dsimp
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hsum, hsigma, hmu, hcost⟩ :=
    mme_stothers_phi233_same_marginal_entropy_minimal
      E H L hE hH hEL hHL
  refine ⟨a, b, c, d, ha, hb, hc, hd, hsum, hsigma, hmu, ?_⟩
  intro a' b' c' d' ha' hb' hc' hd' hsum' hsigma' hmu'
  exact mme_phi233_profile_product_mono_of_entropy_cost_le
    a b c d a' b' c' d' ha hb hc hd ha' hb' hc' hd'
      (hcost a' b' c' d' ha' hb' hc' hd' hsum' hsigma' hmu')
