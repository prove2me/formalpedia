-- Prove2me | Theorems.Thm_RLHF_abs_kl_sub_half_variance
-- name    : RLHF.abs_kl_sub_half_variance
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:54:24.953798+00:00
-- url     : https://prove2.me/theorems/03dd26d1-42a0-48f5-8c5c-b78e83435767
-- title:
--   The exact second-order KL drift law.
-- statement:
--   **The exact second-order KL drift law.**  For any temperature above the reward
--   range,
--   `|KL(π_β‖p) − Var_p(r)/(2β²)| ≤ 2·range(r)·Var_p(r)/β³ + 3·Var_p(r)²/β⁴`.
--   In particular the absolute constant of the KL drift law is `1/2`, not `1`.
--
--   ```lean
--   theorem RLHF.abs_kl_sub_half_variance{β : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p)
--       (hr : rewardRange r ≤ β) :
--       |klDiv (gibbsPolicy β r p) p - variance p r / β ^ 2 / 2|
--         ≤ 2 * (rewardRange r * variance p r / β ^ 3) + 3 * (variance p r ^ 2 / β ^ 4) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/RLHFKLSecondOrder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/RLHFKLSecondOrder.lean#L224

-- Thm stub generated from Algebra/RLHFKLSecondOrder.lean
import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
import Definitions.Def_Algebra_RLHFKLSecondOrder
import Definitions.Def_Algebra_RLHFMeanAbsoluteDeviation

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

theorem RLHF.abs_kl_sub_half_variance{β : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p)
    (hr : rewardRange r ≤ β) :
    |klDiv (gibbsPolicy β r p) p - variance p r / β ^ 2 / 2|
      ≤ 2 * (rewardRange r * variance p r / β ^ 3) + 3 * (variance p r ^ 2 / β ^ 4) := by sorry
