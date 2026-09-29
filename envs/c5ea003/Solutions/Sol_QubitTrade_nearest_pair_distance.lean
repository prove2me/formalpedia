-- Prove2me | solution 1 for QubitTrade.nearest_pair_distance
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:26:11.534345+00:00
-- url     : https://prove2.me/submissions/e8977c87-7b50-432c-a703-ad01d9162768

-- Sol generated from Algebra/QubitTrade/Resolution.lean
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




open QubitTrade in
theorem solution{R : ℕ} (hR : 2 ≤ R) :
    ((orderFrac 1 R : ℚ) : ℝ) < ((orderFrac 1 (R - 1) : ℚ) : ℝ) ∧
      ((orderFrac 1 (R - 1) : ℚ) : ℝ) - ((orderFrac 1 R : ℚ) : ℝ)
        = ((R : ℝ) * ((R : ℝ) - 1))⁻¹ := by
  have hR1 : ((R : ℝ) - 1) = ((R - 1 : ℕ) : ℝ) := by
    have : (1:ℕ) ≤ R := by omega
    push_cast [Nat.cast_sub this]; ring
  have hRpos : (0:ℝ) < R := by
    have : (0:ℕ) < R := by omega
    exact_mod_cast this
  have hR1pos : (0:ℝ) < (R : ℝ) - 1 := by
    have : (2:ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have e₁ : ((orderFrac 1 R : ℚ) : ℝ) = ((R : ℝ))⁻¹ := by
    unfold orderFrac; push_cast; ring
  have e₂ : ((orderFrac 1 (R - 1) : ℚ) : ℝ) = ((R : ℝ) - 1)⁻¹ := by
    unfold orderFrac; push_cast [← hR1]; ring
  constructor
  · rw [e₁, e₂]
    exact inv_strictAnti₀ hR1pos (by linarith)
  · rw [e₁, e₂]
    field_simp
    ring
