-- Prove2me | Theorems.Thm_QubitTrade_cf_target_ambiguous
-- name    : QubitTrade.cf_target_ambiguous
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:51:55.228973+00:00
-- url     : https://prove2.me/theorems/5f103caa-41dc-4d5d-9bc9-e282f2a5a7bd
-- title:
--   Ambiguity below the quadratic threshold.
-- statement:
--   **Ambiguity below the quadratic threshold.**  If `2^t < R(R-1)`, then there is
--   a phase `x` compatible with the two *distinct* order fractions `1/R` and `1/(R-1)`.
--   Both have coprime numerator, so both denominators are honest orders: a `t`-bit
--   register cannot decide between the orders `R` and `R-1`.
--
--   ```lean
--   theorem QubitTrade.cf_target_ambiguous{R t : ℕ} (hR : 2 ≤ R) (h : ((2:ℝ)) ^ t < (R : ℝ) * ((R : ℝ) - 1)) :
--       ∃ x : ℝ, orderFrac 1 R ≠ orderFrac 1 (R - 1) ∧
--         (orderFrac 1 R).den = R ∧ (orderFrac 1 (R - 1)).den = R - 1 ∧
--         Compatible t x (orderFrac 1 R) ∧ Compatible t x (orderFrac 1 (R - 1)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/QubitTrade/Resolution.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/QubitTrade/Resolution.lean#L183

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

theorem QubitTrade.cf_target_ambiguous{R t : ℕ} (hR : 2 ≤ R) (h : ((2:ℝ)) ^ t < (R : ℝ) * ((R : ℝ) - 1)) :
    ∃ x : ℝ, orderFrac 1 R ≠ orderFrac 1 (R - 1) ∧
      (orderFrac 1 R).den = R ∧ (orderFrac 1 (R - 1)).den = R - 1 ∧
      Compatible t x (orderFrac 1 R) ∧ Compatible t x (orderFrac 1 (R - 1)) := by sorry
