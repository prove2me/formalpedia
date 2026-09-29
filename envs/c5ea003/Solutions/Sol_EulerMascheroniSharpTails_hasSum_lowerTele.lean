-- Prove2me | solution 1 for EulerMascheroniSharpTails.hasSum_lowerTele
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:49:35.607436+00:00
-- url     : https://prove2.me/submissions/a64e34dd-893d-432e-85f0-abe32077a243

-- Sol generated from Novelty/EulerMascheroniSharpTails.lean
import Mathlib
import Definitions.Def_Novelty_EulerMascheroniInformationBridge
import Definitions.Def_Novelty_EulerMascheroniSharpTails
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

/-- A nonincreasing sequence tending to `0` gives a telescoping `HasSum`. -/
theorem hasSum_telescoping (u : ℕ → ℝ) (hanti : ∀ k, u (k + 1) ≤ u k)
    (h0 : Filter.Tendsto u Filter.atTop (𝓝 0)) : HasSum (fun i => u i - u (i + 1)) (u 0) := by
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun i => by linarith [hanti i]) _).mpr ?_
  have hsum : ∀ M, ∑ i ∈ Finset.range M, (u i - u (i + 1)) = u 0 - u M :=
    fun M => Finset.sum_range_sub' u M
  simp_rw [hsum]
  simpa using (tendsto_const_nhds (x := u 0) (f := Filter.atTop (α := ℕ))).sub h0

theorem tendsto_inv_linear (c : ℝ) (hc : 0 < c) (n : ℕ) :
    Filter.Tendsto (fun i : ℕ => 1 / (c * ((i : ℝ) + n + 1))) Filter.atTop (𝓝 0) := by
  have h : Filter.Tendsto (fun i : ℕ => ((i : ℝ) + n + 1)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_add_const_right
    apply Filter.tendsto_atTop_add_const_right
    exact tendsto_natCast_atTop_atTop
  exact ((h.const_mul_atTop hc).inv_tendsto_atTop).congr fun i => (one_div _).symm




/-! ## 5. The tail `γ - eulerMascheroniSeq n` -/








/-! ## 6. Quantitative remainder and midpoint acceleration -/






/-! ## 7. Symmetrized information tail (Future direction 4) -/









/-! ## 8. Matching lower bound: the acceleration error is exactly of order `n⁻²` -/






/-! ## 9. Apéry-style linear forms: criterion and a concrete obstruction -/




open EulerMascheroniSharpTails in
theorem solution(n : ℕ) :
    HasSum (fun i : ℕ => 1 / (2 * ((i : ℝ) + n + 1)) - 1 / (2 * ((i : ℝ) + n + 2)))
      (1 / (2 * ((n : ℝ) + 1))) := by
  have hanti : ∀ k : ℕ, 1 / (2 * (((k + 1 : ℕ) : ℝ) + n + 1)) ≤ 1 / (2 * ((k : ℝ) + n + 1)) := by
    intro k
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    refine one_div_le_one_div_of_le (by positivity) ?_
    push_cast
    linarith
  have h := hasSum_telescoping (fun i : ℕ => 1 / (2 * ((i : ℝ) + n + 1))) hanti
    (tendsto_inv_linear 2 (by norm_num) n)
  have hfun : (fun i : ℕ => 1 / (2 * ((i : ℝ) + n + 1)) - 1 / (2 * (((i + 1 : ℕ) : ℝ) + n + 1)))
      = fun i : ℕ => 1 / (2 * ((i : ℝ) + n + 1)) - 1 / (2 * ((i : ℝ) + n + 2)) := by
    funext i
    push_cast
    ring_nf
  rw [hfun] at h
  simpa using h
