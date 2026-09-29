-- Prove2me | solution 1 for RLHF.kl_tendsto_half_variance
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:24:09.253543+00:00
-- url     : https://prove2.me/submissions/848c5291-ebd9-4ea8-94d4-b44984b54a81

-- Sol generated from Algebra/RLHFKLSecondOrder.lean
import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
import Definitions.Def_Algebra_RLHFKLSecondOrder
import Definitions.Def_Algebra_RLHFMeanAbsoluteDeviation
import Theorems.Thm_RLHF_abs_kl_sub_half_variance

/-!
# The exact second-order KL drift constant is `Var/2`

Domain: Algebra (convex analysis × information theory × alignment theory).

The catalogue's `RLHF.kl_gibbs_le_variance` bounds the alignment KL drift by
`e^{range r/β} Var_p(r)/β²`, i.e. by `Var_p(r)/β²` with an absolute constant `1` in the
large-`β` limit.  The cumulant heuristic predicts that the true constant is `1/2` — the
second cumulant of the tilted family — and this file proves it, quantitatively.

* `RLHF.klDiv_gibbs_eq_centred` — the exact identity
  `KL(π_β‖p) = A_β/W_β − log W_β` with `W_β = 𝔼_p e^{(r−𝔼r)/β}` the centred partition
  function and `A_β = 𝔼_p[e^{(r−𝔼r)/β}·(r−𝔼r)/β]`;
* `RLHF.abs_kl_sub_half_variance` — `|KL(π_β‖p) − Var_p(r)/(2β²)| ≤
  2·range(r)·Var_p(r)/β³ + 3·Var_p(r)²/β⁴` whenever `β ≥ range r`;
* `RLHF.kl_tendsto_half_variance` — hence `β²·KL(π_β‖p) → Var_p(r)/2`.

So the KL drift law is exactly `Var_p(r)/(2β²)`: the variance functional of C1 is
correct for KL (unlike the `ℓ¹` law, whose sharp functional is the mean absolute
deviation, see `Algebra.RLHFMeanAbsoluteDeviation`), and the absolute constant is `1/2`,
half of what the catalogue bound gives.

Combining with Pinsker, `‖π_β − p‖₁ ≤ √(2 KL) ≈ σ_p(r)/β`, which is exactly the
standard-deviation law of C1 — and `RLHF.mad_le_sqrt_variance` shows the true `ℓ¹`
constant `MAD_p(r)` is never larger.  The Pinsker step is therefore the *only* source of
looseness in the σ-law, and its defect is precisely the deviation defect
`σ_p(r) − MAD_p(r)`.

All error terms are third-order Taylor remainders, handled by `Real.exp_bound`.
-/

open RLHF

open Finset

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-! ## 1. Centred moment sums -/




/-! ## 2. The centred first moment of the tilt -/





/-! ## 3. The exact KL identity and its second-order expansion -/





open RLHF in
theorem solution{r p : Ω → ℝ} (hp : IsPosDist p) :
    Filter.Tendsto (fun β : ℝ => β ^ 2 * klDiv (gibbsPolicy β r p) p) Filter.atTop
      (nhds (variance p r / 2)) := by
  have hinv : Filter.Tendsto (fun β : ℝ => (1 : ℝ) / β) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
  have herr : Filter.Tendsto
      (fun β : ℝ => 2 * (rewardRange r * variance p r) * (1 / β)
        + 3 * variance p r ^ 2 * ((1 / β) * (1 / β))) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun β : ℝ => 2 * (rewardRange r * variance p r) * (1 / β))
        Filter.atTop (nhds 0) := by
      simpa using hinv.const_mul (2 * (rewardRange r * variance p r))
    have h2 : Filter.Tendsto (fun β : ℝ => 3 * variance p r ^ 2 * ((1 / β) * (1 / β)))
        Filter.atTop (nhds 0) := by
      simpa using (hinv.mul hinv).const_mul (3 * variance p r ^ 2)
    simpa using h1.add h2
  have hlow : Filter.Tendsto
      (fun β : ℝ => variance p r / 2 - (2 * (rewardRange r * variance p r) * (1 / β)
        + 3 * variance p r ^ 2 * ((1 / β) * (1 / β)))) Filter.atTop
      (nhds (variance p r / 2)) := by
    simpa using tendsto_const_nhds.sub herr
  have hhigh : Filter.Tendsto
      (fun β : ℝ => variance p r / 2 + (2 * (rewardRange r * variance p r) * (1 / β)
        + 3 * variance p r ^ 2 * ((1 / β) * (1 / β)))) Filter.atTop
      (nhds (variance p r / 2)) := by
    simpa using tendsto_const_nhds.add herr
  have hsandwich : ∀ β : ℝ, max (rewardRange r) 1 ≤ β →
      |β ^ 2 * klDiv (gibbsPolicy β r p) p - variance p r / 2|
        ≤ 2 * (rewardRange r * variance p r) * (1 / β)
          + 3 * variance p r ^ 2 * ((1 / β) * (1 / β)) := by
    intro β hβm
    have hβ : 0 < β := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hβm)
    have hr : rewardRange r ≤ β := le_trans (le_max_left _ _) hβm
    have hβ2 : (0:ℝ) < β ^ 2 := by positivity
    have hkey := abs_kl_sub_half_variance hβ hp hr
    have heq : β ^ 2 * (klDiv (gibbsPolicy β r p) p - variance p r / β ^ 2 / 2)
        = β ^ 2 * klDiv (gibbsPolicy β r p) p - variance p r / 2 := by
      field_simp
    have habs : |β ^ 2 * (klDiv (gibbsPolicy β r p) p - variance p r / β ^ 2 / 2)|
        = β ^ 2 * |klDiv (gibbsPolicy β r p) p - variance p r / β ^ 2 / 2| := by
      rw [abs_mul, abs_of_pos hβ2]
    rw [← heq, habs]
    refine le_trans (mul_le_mul_of_nonneg_left hkey hβ2.le) (le_of_eq ?_)
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (max (rewardRange r) 1)] with β hβm
    linarith [(abs_le.1 (hsandwich β hβm)).1]
  · filter_upwards [Filter.eventually_ge_atTop (max (rewardRange r) 1)] with β hβm
    linarith [(abs_le.1 (hsandwich β hβm)).2]
