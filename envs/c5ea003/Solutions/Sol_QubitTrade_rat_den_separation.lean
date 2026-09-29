-- Prove2me | solution 1 for QubitTrade.rat_den_separation
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:30:13.005705+00:00
-- url     : https://prove2.me/submissions/a4554dad-7352-4784-9382-0d1a7926c4e9

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
theorem solution(a b : ℚ) (h : a ≠ b) :
    ((a.den : ℝ) * b.den)⁻¹ ≤ |(a : ℝ) - b| := by
  have ha : a * (a.den : ℚ) = (a.num : ℚ) := Rat.mul_den_eq_num a
  have hb : b * (b.den : ℚ) = (b.num : ℚ) := Rat.mul_den_eq_num b
  have hda : (0:ℚ) < a.den := by exact_mod_cast a.pos
  have hdb : (0:ℚ) < b.den := by exact_mod_cast b.pos
  set z : ℤ := a.num * b.den - b.num * a.den with hz
  have key : (a - b) * ((a.den : ℚ) * b.den) = (z : ℚ) := by
    rw [hz]; push_cast [← ha, ← hb]; ring
  have hzne : (z : ℚ) ≠ 0 := by
    rw [← key]; exact mul_ne_zero (sub_ne_zero.mpr h) (by positivity)
  have h1 : (1:ℚ) ≤ |(z:ℚ)| := by
    have hz0 : z ≠ 0 := by exact_mod_cast hzne
    have : (1:ℤ) ≤ |z| := Int.one_le_abs (by omega)
    exact_mod_cast this
  have habs : |a - b| * ((a.den : ℚ) * b.den) = |(z:ℚ)| := by
    rw [← key, abs_mul, abs_of_pos (show (0:ℚ) < (a.den:ℚ) * b.den by positivity)]
  have hQ : (((a.den : ℚ)) * b.den)⁻¹ ≤ |a - b| := by
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    calc (1:ℚ) ≤ |(z:ℚ)| := h1
      _ = |a - b| * ((a.den:ℚ) * b.den) := habs.symm
  have hR : ((((a.den : ℚ)) * b.den)⁻¹ : ℝ) ≤ ((|a - b| : ℚ) : ℝ) := by exact_mod_cast hQ
  push_cast at hR
  simpa using hR
