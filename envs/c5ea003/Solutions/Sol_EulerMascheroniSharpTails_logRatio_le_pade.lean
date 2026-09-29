-- Prove2me | solution 1 for EulerMascheroniSharpTails.logRatio_le_pade
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:36:02.283561+00:00
-- url     : https://prove2.me/submissions/fafac1dd-fbaf-466b-8138-ed31325c6bfb

-- Sol generated from Novelty/EulerMascheroniSharpTails.lean
import Mathlib
import Definitions.Def_Novelty_EulerMascheroniInformationBridge
import Definitions.Def_Novelty_EulerMascheroniSharpTails
import Theorems.Thm_EulerMascheroniSharpTails_hasDerivAt_logRatio
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
theorem solution(z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Real.log (1 + z) - Real.log (1 - z) ≤ 2 * z + 2 * z ^ 3 / 3 + 2 * z ^ 5 / (5 * (1 - z ^ 2)) := by
  set f : ℝ → ℝ := fun x => 2 * x + 2 * x ^ 3 / 3 + 2 * x ^ 5 / (5 * (1 - x ^ 2))
      - (Real.log (1 + x) - Real.log (1 - x)) with hf
  have key : ∀ x ∈ Set.Icc (0 : ℝ) z, HasDerivAt f (4 * x ^ 6 / (5 * (1 - x ^ 2) ^ 2)) x := by
    intro x hx
    obtain ⟨hxl, hxr⟩ := hx
    have hx0 : (-1 : ℝ) < x := by linarith
    have hx1 : x < 1 := lt_of_le_of_lt hxr hz1
    have hne3 : (1 : ℝ) - x ^ 2 ≠ 0 := by nlinarith
    have hne4 : (5 : ℝ) * (1 - x ^ 2) ≠ 0 :=
      mul_ne_zero (by norm_num : (5 : ℝ) ≠ 0) hne3
    have h1 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
    have h2 : HasDerivAt (fun y : ℝ => 2 * y ^ 3 / 3) (2 * x ^ 2) x := by
      have hp : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by simpa using hasDerivAt_pow 3 x
      have hq := (hp.const_mul (2 : ℝ)).div_const 3
      convert hq using 1
      ring
    have hnum : HasDerivAt (fun y : ℝ => 2 * y ^ 5) (10 * x ^ 4) x := by
      have hp : HasDerivAt (fun y : ℝ => y ^ 5) (5 * x ^ 4) x := by simpa using hasDerivAt_pow 5 x
      have hq := hp.const_mul (2 : ℝ)
      convert hq using 1
      ring
    have hden : HasDerivAt (fun y : ℝ => 5 * (1 - y ^ 2)) (-(10 * x)) x := by
      have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
      have hq := (hp.const_sub (1 : ℝ)).const_mul (5 : ℝ)
      convert hq using 1
      ring
    have h := ((h1.add h2).add (hnum.div hden hne4)).sub (hasDerivAt_logRatio x hx0 hx1)
    convert h using 1
    field_simp
    ring
  have hmono : MonotoneOn f (Set.Icc 0 z) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x hx => (key x hx).continuousAt.continuousWithinAt
    · exact fun x hx => ((key x (interior_subset hx)).differentiableAt).differentiableWithinAt
    · intro x hx
      rw [(key x (interior_subset hx)).deriv]
      obtain ⟨hxl, hxr⟩ := interior_subset hx
      have hx1 : x < 1 := lt_of_le_of_lt hxr hz1
      have hpos : (0 : ℝ) < 1 - x ^ 2 := by nlinarith
      positivity
  have h0 : f 0 = 0 := by simp [hf]
  have hle := hmono (Set.left_mem_Icc.mpr hz0) (Set.right_mem_Icc.mpr hz0) hz0
  rw [h0] at hle
  simp only [hf] at hle
  linarith
