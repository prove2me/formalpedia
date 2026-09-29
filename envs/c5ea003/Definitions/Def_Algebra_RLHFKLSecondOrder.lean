-- Prove2me | Definitions.Def_Algebra_RLHFKLSecondOrder
-- name    : Algebra_RLHFKLSecondOrder
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T09:36:02.277741+00:00
-- url     : https://prove2.me/theorems/d4de8a4a-d501-4528-a069-e0f3ec95851f
-- title:
--   Aether Catalog definitions — Algebra_RLHFKLSecondOrder
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.RLHFKLSecondOrder`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/RLHFKLSecondOrder.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
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

namespace RLHF

open Finset

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-! ## 1. Centred moment sums -/




/-! ## 2. The centred first moment of the tilt -/

/-- `A_β = 𝔼_p[e^{(r−𝔼r)/β} · (r−𝔼r)/β]`, the centred first moment of the tilted
reward.  It is the numerator of the exact KL identity. -/
noncomputable def tiltMoment (β : ℝ) (r p : Ω → ℝ) : ℝ :=
  ∑ y, p y * (Real.exp ((r y - mean p r) / β) * ((r y - mean p r) / β))




/-! ## 3. The exact KL identity and its second-order expansion -/




end RLHF


