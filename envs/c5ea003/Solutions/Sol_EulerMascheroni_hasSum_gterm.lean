-- Prove2me | solution 1 for EulerMascheroni.hasSum_gterm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:50:24.741203+00:00
-- url     : https://prove2.me/submissions/8bebb969-aae1-4c3e-a041-a3c9b34b4443

-- Sol generated from MachineLearning/EulerMascheroni/SeriesRepresentation.lean
import Mathlib
import Definitions.Def_MachineLearning_EulerMascheroni_SeriesRepresentation

/-!
# A positive-term series representation of the Euler–Mascheroni constant

This file establishes the classical *series acceleration* of the
Euler–Mascheroni constant `γ = eulerMascheroniConstant`:
```
γ = ∑_{k=0}^∞ ( 1/(k+1) − [log(k+2) − log(k+1)] ).
```
Every term `gterm k = 1/(k+1) − log((k+2)/(k+1))` is **strictly positive**
(because `log(1+x) < x`), so the partial sums increase monotonically to `γ`.
The `n`-th partial sum is *exactly* `eulerMascheroniSeq n = H_n − log(n+1)`, the
lower approximant from Mathlib, which makes this the "Apéry-like" monotone
rational-driven approximation to `γ`: the rational engine is the harmonic
number `H_n`, corrected by `log(n+1)`.

-- !-- Lab Notes -- !--
HYPOTHESIS.  `γ`, defined as `lim (H_n − log n)`, should equal a convergent
series of *positive* terms.  Telescoping `log(n+1) = ∑_{k<n}(log(k+2)−log(k+1))`
turns `H_n − log(n+1)` into a partial sum of `gterm`.

EXPERIMENT.  `gterm_partial` (induction + `harmonic_succ`) proves the partial-sum
identity.  `gterm_pos` derives positivity from `Real.log_lt_sub_one_of_pos`.
`hasSum_gterm` upgrades the convergence `eulerMascheroniSeq → γ` to a `HasSum`
statement using `summable_of_sum_range_le` (terms are nonnegative and partial
sums are bounded by `γ`) and uniqueness of limits.

ANALYSIS.  The representation is genuine but converges only like `1/k` (the term
`gterm k ~ 1/(2(k+1)^2)`, summable but slow).  The monotone lower approximants
`eulerMascheroniSeq n` are `H_n − log(n+1)`; their *rational* part `H_n` is the
Apéry-like data, but the additive logarithm prevents a purely rational sandwich
— this is the structural obstruction to an elementary irrationality proof.

CRITIQUE.  `hasSum_gterm` is not vacuous: it pins the sum to the specific value
`γ`, not merely "some real".  Positivity (`gterm_pos`) and strict monotonicity
(`strictMono_eulerMascheroniSeq`) are quantitative and use real inequalities.

SYNTHESIS.  We obtain a clean positive-term series for `γ`, the exact
identification of its partial sums with Mathlib's lower approximant, and strict
monotonicity of that approximant.
-/

open Filter Topology Real

open EulerMascheroni


/-- Each term is strictly positive, since `log(1 + 1/(k+1)) < 1/(k+1)`. -/
theorem gterm_pos (k : ℕ) : 0 < gterm k := by
  unfold gterm
  rw [← Real.log_div (by positivity) (by positivity)]
  have hne : (k + 2 : ℝ) / (k + 1) ≠ 1 := by
    rw [ne_eq, div_eq_one_iff_eq (by positivity)]; intro h; linarith
  have hlog := Real.log_lt_sub_one_of_pos (x := (k + 2 : ℝ) / (k + 1)) (by positivity) hne
  have heq : (k + 2 : ℝ) / (k + 1) - 1 = 1 / (k + 1) := by field_simp; ring
  rw [heq] at hlog; linarith

/-- The `n`-th partial sum of `gterm` is exactly the Mathlib lower approximant
`eulerMascheroniSeq n = H_n − log(n+1)`.  This is the telescoping identity. -/
theorem gterm_partial (n : ℕ) :
    ∑ k ∈ Finset.range n, gterm k = Real.eulerMascheroniSeq n := by
  simp only [gterm, Real.eulerMascheroniSeq]
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, harmonic_succ]
    push_cast
    rw [show ((m : ℝ) + 1 + 1) = (m : ℝ) + 2 by ring]
    ring







open EulerMascheroni in
theorem solution: HasSum gterm Real.eulerMascheroniConstant := by
  have hsummable : Summable gterm := by
    apply summable_of_sum_range_le (c := Real.eulerMascheroniConstant)
    · intro n; exact (gterm_pos n).le
    · intro n
      rw [gterm_partial n]
      exact (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n).le
  have h1 := hsummable.hasSum
  have h2 := h1.tendsto_sum_nat
  have h3 : Tendsto (fun n => ∑ k ∈ Finset.range n, gterm k) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
    simp only [gterm_partial]; exact Real.tendsto_eulerMascheroniSeq
  have huniq := tendsto_nhds_unique h2 h3
  rw [← huniq]; exact h1
