-- Prove2me | solution 1 for QubitTrade.cf_target_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:36:05.621351+00:00
-- url     : https://prove2.me/submissions/d5281e77-cbc2-481e-8d76-3a9bf800a578

-- Sol generated from Algebra/QubitTrade/Resolution.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_Resolution
import Theorems.Thm_QubitTrade_rat_den_separation

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
theorem solution{R t : ℕ} (hRt : ((R : ℝ)) ^ 2 ≤ 2 ^ t) {x : ℝ} {q₁ q₂ : ℚ}
    (h₁ : q₁.den ≤ R) (h₂ : q₂.den ≤ R)
    (c₁ : Compatible t x q₁) (c₂ : Compatible t x q₂) : q₁ = q₂ := by
  by_contra hne
  have hd₁ : (0:ℝ) < q₁.den := by exact_mod_cast q₁.pos
  have hd₂ : (0:ℝ) < q₂.den := by exact_mod_cast q₂.pos
  have hR₁ : ((q₁.den : ℝ)) ≤ R := by exact_mod_cast h₁
  have hR₂ : ((q₂.den : ℝ)) ≤ R := by exact_mod_cast h₂
  have hRpos : (0:ℝ) < R := lt_of_lt_of_le hd₁ hR₁
  -- the two candidates are close
  have hclose : |(q₁ : ℝ) - q₂| < ((2:ℝ) ^ t)⁻¹ := by
    have htri : |(q₁ : ℝ) - q₂| ≤ |x - q₁| + |x - q₂| := by
      have : (q₁ : ℝ) - q₂ = (x - q₂) - (x - q₁) := by ring
      rw [this]
      calc |(x - (q₂:ℝ)) - (x - q₁)| ≤ |x - (q₂:ℝ)| + |x - (q₁:ℝ)| := abs_sub _ _
        _ = |x - (q₁:ℝ)| + |x - (q₂:ℝ)| := by ring
    have hsum : |x - (q₁:ℝ)| + |x - (q₂:ℝ)| < res t + res t := by
      exact add_lt_add c₁ c₂
    have hres : res t + res t = ((2:ℝ) ^ t)⁻¹ := by
      unfold res
      rw [pow_succ]
      field_simp
      ring
    linarith [htri, hres ▸ hsum]
  -- but they are far apart
  have hfar : ((q₁.den : ℝ) * q₂.den)⁻¹ ≤ |(q₁ : ℝ) - q₂| := rat_den_separation q₁ q₂ hne
  have hprod : ((q₁.den : ℝ)) * q₂.den ≤ (R:ℝ) ^ 2 := by
    have := mul_le_mul hR₁ hR₂ (le_of_lt hd₂) (le_of_lt hRpos)
    nlinarith
  have hlow : ((R:ℝ) ^ 2)⁻¹ ≤ ((q₁.den : ℝ) * q₂.den)⁻¹ :=
    inv_anti₀ (by positivity) hprod
  have : ((2:ℝ) ^ t)⁻¹ ≤ ((R:ℝ)^2)⁻¹ := inv_anti₀ (by positivity) hRt
  linarith
