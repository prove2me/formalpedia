-- Prove2me | Theorems.Thm_QubitTrade_linear_register_ambiguous
-- name    : QubitTrade.linear_register_ambiguous
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:52:34.932831+00:00
-- url     : https://prove2.me/theorems/f882f301-8b97-4acf-b5ca-e08615733cba
-- title:
--   Refutation of the linear-register prediction.
-- statement:
--   **Refutation of the linear-register prediction.**  A register of
--   `log₂ R + c` bits is ambiguous for every `R > 2 ^ c + 1`: no constant, and indeed no
--   `O(log log R)` additive correction, can rescue a register of size `log₂ R + o(log R)`.
--   Stated with the concrete witness `2 ^ t ≤ 2 ^ c * R`.
--
--   ```lean
--   theorem QubitTrade.linear_register_ambiguous{R t c : ℕ} (hR : 2 ^ c + 1 < R)
--       (ht : ((2:ℝ)) ^ t ≤ 2 ^ c * (R : ℝ)) :
--       ∃ (x : ℝ) (q₁ q₂ : ℚ), q₁ ≠ q₂ ∧ q₁.den ≤ R ∧ q₂.den ≤ R ∧
--         Compatible t x q₁ ∧ Compatible t x q₂ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/QubitTrade/Resolution.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/QubitTrade/Resolution.lean#L238

-- Thm stub generated from Algebra/QubitTrade/Resolution.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_Resolution

/-!
# QUBIT-TRADE I: the resolution threshold of continued-fraction order recovery

Shor's order-finding algorithm returns a phase estimate `x ≈ k / r`, where
`r = ord_N(a)` and `0 ≤ k < r`, and the classical post-processing recovers `k/r`
(hence `r`) by continued fractions.  If the phase register is *truncated* to its
top `t` bits, the estimate is only known to accuracy `2^{-(t+1)}`.

The experiment QUBIT-TRADE measured a truncation threshold `t_min ≈ 2·log₂ r`.
This file proves that this threshold is **exact**, as a two-sided statement about
the *information* carried by a `t`-bit phase:

* `QubitTrade.rat_den_separation` — two distinct rationals are at distance at
  least `1/(den₁ · den₂)` (the Farey separation bound);
* `QubitTrade.cf_target_unique` — **sufficiency**: if `R^2 ≤ 2^t`, i.e.
  `t ≥ 2 log₂ R`, then at most one rational of denominator `≤ R` is compatible
  with a `t`-bit phase, so the continued-fraction target — and with it the order
  — is uniquely determined;
* `QubitTrade.order_unique_of_resolution` — the order-level corollary;
* `QubitTrade.cf_target_ambiguous` — **necessity**: if `2^t < R(R-1)`, i.e.
  `t < 2 log₂ R` up to one bit, there is a phase compatible with *two* distinct
  reduced fractions of denominator `≤ R`, realised by two distinct orders
  `R` and `R-1`.  No post-processing can separate them.
* `QubitTrade.threshold_two_sided` — the two statements packaged: the threshold
  sits in the window `R(R-1) ≤ 2^t < R^2`, i.e. `t_min = ⌈2 log₂ R⌉ ± 1`.
* `QubitTrade.linear_register_ambiguous` — the refutation of the predicted
  `log r + O(log log r)` register: for every constant `c`, a register of
  `log₂ R + c` bits is ambiguous as soon as `R > 2^c + 1`.

Everything is unconditional and model-free: it is a statement about how many
rationals of bounded denominator fit inside an interval of width `2^{-t}`.
-/

open QubitTrade

open scoped Rat

/-! ## Farey separation -/


/-! ## The truncated-register measurement model -/







/-! ## Sufficiency: `t ≥ 2 log₂ R` determines the continued-fraction target -/



/-! ## Necessity: below the quadratic threshold the target is ambiguous -/



/-! ## The two-sided threshold -/

theorem QubitTrade.linear_register_ambiguous{R t c : ℕ} (hR : 2 ^ c + 1 < R)
    (ht : ((2:ℝ)) ^ t ≤ 2 ^ c * (R : ℝ)) :
    ∃ (x : ℝ) (q₁ q₂ : ℚ), q₁ ≠ q₂ ∧ q₁.den ≤ R ∧ q₂.den ≤ R ∧
      Compatible t x q₁ ∧ Compatible t x q₂ := by sorry
