-- Prove2me | solution 1 for EulerMascheroniSharpTails.log_succ_div_le_pade
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:37:38.134611+00:00
-- url     : https://prove2.me/submissions/c7c4a18d-630f-4fb9-aef9-79284edbdb0f

-- Sol generated from Novelty/EulerMascheroniSharpTails.lean
import Mathlib
import Definitions.Def_Novelty_EulerMascheroniInformationBridge
import Definitions.Def_Novelty_EulerMascheroniSharpTails
import Theorems.Thm_EulerMascheroniSharpTails_logRatio_le_pade
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





/-! ## 4. Telescoping comparison series -/






/-! ## 5. The tail `γ - eulerMascheroniSeq n` -/








/-! ## 6. Quantitative remainder and midpoint acceleration -/






/-! ## 7. Symmetrized information tail (Future direction 4) -/









/-! ## 8. Matching lower bound: the acceleration error is exactly of order `n⁻²` -/






/-! ## 9. Apéry-style linear forms: criterion and a concrete obstruction -/




open EulerMascheroniSharpTails in
theorem solution(m : ℝ) (hm : 1 ≤ m) :
    Real.log ((m + 1) / m)
      ≤ 2 / (2 * m + 1) + 2 / (3 * (2 * m + 1) ^ 3)
        + 1 / (10 * m * (m + 1) * (2 * m + 1) ^ 3) := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hd : (0 : ℝ) < 2 * m + 1 := by linarith
  set z : ℝ := 1 / (2 * m + 1) with hz
  have hz0 : 0 ≤ z := by positivity
  have hz1 : z < 1 := by
    rw [hz, div_lt_one hd]; linarith
  have h1 : (1 : ℝ) + z = (2 * m + 2) / (2 * m + 1) := by
    rw [hz]; field_simp; ring
  have h2 : (1 : ℝ) - z = 2 * m / (2 * m + 1) := by
    rw [hz]; field_simp; ring
  have hratio : Real.log (1 + z) - Real.log (1 - z) = Real.log ((m + 1) / m) := by
    rw [h1, h2, ← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  have hsq : (1 : ℝ) - z ^ 2 = 4 * m * (m + 1) / (2 * m + 1) ^ 2 := by
    rw [hz]; field_simp; ring
  have hrhs : 2 * z + 2 * z ^ 3 / 3 + 2 * z ^ 5 / (5 * (1 - z ^ 2))
      = 2 / (2 * m + 1) + 2 / (3 * (2 * m + 1) ^ 3)
        + 1 / (10 * m * (m + 1) * (2 * m + 1) ^ 3) := by
    rw [hsq, hz]
    field_simp
    ring
  have h := logRatio_le_pade z hz0 hz1
  rw [hratio, hrhs] at h
  exact h
