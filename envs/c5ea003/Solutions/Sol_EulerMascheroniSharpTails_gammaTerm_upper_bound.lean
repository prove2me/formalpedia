-- Prove2me | solution 1 for EulerMascheroniSharpTails.gammaTerm_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:49:35.028454+00:00
-- url     : https://prove2.me/submissions/0253818a-0750-49a2-8c2f-06ab25229cf0

-- Sol generated from Novelty/EulerMascheroniSharpTails.lean
import Mathlib
import Definitions.Def_Novelty_EulerMascheroniInformationBridge
import Definitions.Def_Novelty_EulerMascheroniSharpTails
import Theorems.Thm_EulerMascheroniSharpTails_le_log_succ_div
/-
# Sharp two-sided summand asymptotics and quantitative tails for `γ`

This file continues the research thread on the Euler–Mascheroni constant that was
started in `Novelty/EulerMascheroniInformationBridge.lean`, where `γ` was realised
as the accumulated Kullback–Leibler divergence

  `γ = ∑ k, D(Exp(k+1) ‖ Exp(k+2))`,   `gammaTerm k = 1/(k+1) - log((k+2)/(k+1))`.

We prove here the four "future directions" that were left open there.

## Main results

* `gammaTerm_lower_bound` / `gammaTerm_upper_bound` — the *purely rational squeeze*
  `1/(2(k+2)^2) ≤ gammaTerm k ≤ 1/(2(k+1)^2)`, together with the sharper
  `gammaTerm_ge_tele : 1/(2(k+1)(k+2)) ≤ gammaTerm k`.
* `remainder_pos` and `remainder_le_inv_two_mul` — for `1 ≤ n`,
  `0 < γ - eulerMascheroniSeq n ≤ 1/(2n)`.
* `accelerated`, `abs_accelerated_error_le` — the midpoint-corrected sequence
  `accelerated n = eulerMascheroniSeq n + 1/(2(n+1))` satisfies the *explicit*
  `O(n⁻²)` bound `|γ - accelerated n| ≤ 1/(12(n+1)^2)` for **every** `n : ℕ`
  (no threshold is needed), and in fact `accelerated n ≤ γ`.
* `symKL_eq_sq_div` — the symmetrized divergence identity `D(a‖b)+D(b‖a) = (a-b)²/(ab)`,
  `summable_symKL_iff_of_ratio_bounds` — an exact summability criterion for chains of
  positive rates with bounded ratios, and its two test cases
  `hasSum_symKL_linear_rates` (polynomial rates: convergent, with sum exactly `1`)
  and `not_summable_symKL_geometric_rates` (geometric rates: always divergent).

## Method

Everything rests on two calculus lemmas for the *logarithmic ratio*
`Λ z = log(1+z) - log(1-z)` on `[0,1)`:

  `2z + 2z³/3 ≤ Λ z ≤ 2z/(1-z²)`,

each proved by exhibiting the derivative of the difference as an explicitly
nonnegative rational function (`4z⁴/(1-z²)` resp. `4z²/(1-z²)²`).  Substituting
`z = 1/(2m+1)` turns these into the two-sided rational estimate

  `2/(2m+1) + 2/(3(2m+1)³) ≤ log((m+1)/m) ≤ (2m+1)/(2m(m+1))`,

which is exactly what is needed to sandwich `gammaTerm` between two *telescoping*
sequences.  The upper telescoping sequence is the midpoint-corrected
`F m = 1/(2m) + 1/(12m²)`; the constant `1/12` is the classical Euler–Maclaurin
coefficient and the resulting bound is asymptotically sharp.
-/

open Real Filter Finset Topology
open EulerMascheroniInformationBridge

open EulerMascheroniSharpTails

/-! ## 1. Two calculus estimates for the logarithmic ratio -/




/-! ## 2. Rational two-sided bounds for `log((m+1)/m)` -/



/-! ## 3. Sharp two-sided bounds for the summands -/

/-- `gammaTerm` written in terms of the real parameter `m = k+1`. -/
theorem gammaTerm_eq_shift (k : ℕ) :
    gammaTerm k = 1 / ((k : ℝ) + 1) - Real.log ((((k : ℝ) + 1) + 1) / ((k : ℝ) + 1)) := by
  unfold gammaTerm
  rw [show ((k : ℝ) + 1 + 1) = (k : ℝ) + 2 by ring]




/-! ## 4. Telescoping comparison series -/






/-! ## 5. The tail `γ - eulerMascheroniSeq n` -/








/-! ## 6. Quantitative remainder and midpoint acceleration -/






/-! ## 7. Symmetrized information tail (Future direction 4) -/









/-! ## 8. Matching lower bound: the acceleration error is exactly of order `n⁻²` -/






/-! ## 9. Apéry-style linear forms: criterion and a concrete obstruction -/




open EulerMascheroniSharpTails in
theorem solution(k : ℕ) : gammaTerm k ≤ 1 / (2 * ((k : ℝ) + 1) ^ 2) := by
  set m : ℝ := (k : ℝ) + 1 with hm
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hm1 : (1 : ℝ) ≤ m := by rw [hm]; linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hlog := le_log_succ_div m hm1
  have hstep : 1 / m - (2 / (2 * m + 1) + 2 / (3 * (2 * m + 1) ^ 3)) ≤ 1 / (2 * m ^ 2) := by
    rw [← sub_nonneg]
    have hkey : 1 / (2 * m ^ 2) - (1 / m - (2 / (2 * m + 1) + 2 / (3 * (2 * m + 1) ^ 3)))
        = (16 * m ^ 2 + 12 * m + 3) / (6 * m ^ 2 * (2 * m + 1) ^ 3) := by
      field_simp
      ring
    rw [hkey]
    positivity
  rw [gammaTerm_eq_shift k, ← hm]
  linarith
