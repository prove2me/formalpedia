-- Prove2me | solution 1 for RLHF.sum_ctr_cube_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:09:42.744149+00:00
-- url     : https://prove2.me/submissions/692a59dd-ca87-43ea-b3b9-e465d7e7736e

-- Sol generated from Algebra/RLHFKLSecondOrder.lean
import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
import Definitions.Def_Algebra_RLHFKLSecondOrder
import Definitions.Def_Algebra_RLHFMeanAbsoluteDeviation
import Theorems.Thm_RLHF_abs_sub_mean_le_range
import Theorems.Thm_RLHF_sum_ctr_sq_div

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
theorem solution{β : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsDist p) :
    ∑ y, p y * |(r y - mean p r) / β| ^ 3 ≤ rewardRange r * variance p r / β ^ 3 := by
  have hle : ∀ y ∈ (univ : Finset Ω), p y * |(r y - mean p r) / β| ^ 3
      ≤ (rewardRange r / β) * (p y * ((r y - mean p r) / β) ^ 2) := by
    intro y _
    have habs : |(r y - mean p r) / β| ≤ rewardRange r / β := by
      rw [abs_div, abs_of_pos hβ]
      exact (div_le_div_iff_of_pos_right hβ).mpr (abs_sub_mean_le_range hp y)
    have hcube : |(r y - mean p r) / β| ^ 3
        = |(r y - mean p r) / β| * ((r y - mean p r) / β) ^ 2 := by
      rw [show (3 : ℕ) = 1 + 2 by norm_num, pow_add, pow_one, sq_abs]
    rw [hcube]
    have h2 : |(r y - mean p r) / β| * ((r y - mean p r) / β) ^ 2
        ≤ (rewardRange r / β) * ((r y - mean p r) / β) ^ 2 :=
      mul_le_mul_of_nonneg_right habs (sq_nonneg _)
    calc p y * (|(r y - mean p r) / β| * ((r y - mean p r) / β) ^ 2)
        ≤ p y * ((rewardRange r / β) * ((r y - mean p r) / β) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (hp.nonneg y)
      _ = (rewardRange r / β) * (p y * ((r y - mean p r) / β) ^ 2) := by ring
  refine le_trans (Finset.sum_le_sum hle) ?_
  rw [← Finset.mul_sum, sum_ctr_sq_div, div_mul_div_comm, ← pow_succ']
