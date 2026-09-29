-- Prove2me | solution 1 for QubitTrade.linear_register_ambiguous
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:39:18.775103+00:00
-- url     : https://prove2.me/submissions/8a6257be-1dbf-4847-8804-6c5f6d6413cd

-- Sol generated from Algebra/QubitTrade/Resolution.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_Resolution
import Theorems.Thm_QubitTrade_cf_target_ambiguous

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
theorem solution{R t c : ℕ} (hR : 2 ^ c + 1 < R)
    (ht : ((2:ℝ)) ^ t ≤ 2 ^ c * (R : ℝ)) :
    ∃ (x : ℝ) (q₁ q₂ : ℚ), q₁ ≠ q₂ ∧ q₁.den ≤ R ∧ q₂.den ≤ R ∧
      Compatible t x q₁ ∧ Compatible t x q₂ := by
  have hR2 : 2 ≤ R := by
    have : 1 ≤ 2 ^ c := Nat.one_le_two_pow
    omega
  have hcR : ((2:ℝ) ^ c : ℝ) < (R : ℝ) - 1 := by
    have h1 : ((2 ^ c + 1 : ℕ) : ℝ) < (R : ℝ) := by exact_mod_cast hR
    push_cast at h1
    linarith
  have hRpos : (0:ℝ) < R := by
    have : (0:ℕ) < R := by omega
    exact_mod_cast this
  have : ((2:ℝ)) ^ t < (R : ℝ) * ((R : ℝ) - 1) := by
    calc ((2:ℝ)) ^ t ≤ 2 ^ c * (R : ℝ) := ht
      _ < ((R : ℝ) - 1) * (R : ℝ) := by
          apply mul_lt_mul_of_pos_right hcR hRpos
      _ = (R : ℝ) * ((R : ℝ) - 1) := by ring
  obtain ⟨x, hne, hd₁, hd₂, c₁, c₂⟩ := cf_target_ambiguous hR2 this
  exact ⟨x, orderFrac 1 R, orderFrac 1 (R - 1), hne, by omega, by omega, c₁, c₂⟩
