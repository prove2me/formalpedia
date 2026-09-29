-- Prove2me | solution 1 for AdjSum.tendsto_mul_div_add_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:37:19.257468+00:00
-- url     : https://prove2.me/submissions/163a43dc-b0a9-4826-adef-2f6a625fe3b0

-- Sol generated from Applications/AdjacentSumPolytopes/DominantGrowth.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_DominantGrowth
import Definitions.Def_Applications_AdjacentSumPolytopes_Growth

/-!
# The dominant growth rate of the adjacent-sum model

The bounds of `Applications.AdjacentSumPolytopes.Growth` bracket the counts between two
exponentials but do not say that a growth *rate* exists.  Here we prove that it does,
by a Fekete (subadditivity) argument applied to the diagonal counts

`diagCount s n = (adjMat s ^ n) 0 0 = #{open points of length n+1 with x₀ = xₙ = 0}`,

which are supermultiplicative because concatenation of two loops at the state `0` is a
loop at `0`.  The resulting limit

`λ_s = exp (lim_{n} (log diagCount s n)/n)`

is the reciprocal of the dominant real pole of the shared characteristic denominator,
and we show `⌊s/2⌋ + 1 ≤ λ_s ≤ s + 1` (in logarithmic form).

-- !-- Lab Notes -- !--
* **Hypothesis.** Loops at the state `0` are supermultiplicative, so Fekete's lemma
  applies and the exponential growth rate exists; the block bounds of the previous file
  bracket it.
* **Experiment.** `diagCount 2 n = 1, 1, 3, 6, 14, 31, 70, 157, ...` and the ratios
  `1, 3, 2, 2.33, 2.21, 2.26, 2.24, ...` oscillate towards the dominant root `≈ 2.2470`
  of `x³ − 2x² − x + 1`, comfortably inside `[2, 3]`.  For `s = 3`:
  `1, 1, 4, 10, 30, 85, 246, 707` with ratios approaching `≈ 2.87 ∈ [2, 4]`.
* **Analysis.** The `Subadditive` machinery of Mathlib needs `BddBelow` of `u n / n`
  where `u n = − log (diagCount s n)`; the upper block bound supplies exactly that.
  The lower bound on the limit needs a shifted subsequence, since `diagCount s 0 = 1`
  carries no information.
* **Critique.** The statement is not vacuous: `diagCount s n ≥ 1` is proved (the all-zero
  point is always admissible), so all logarithms are of positive numbers, and for
  `s ≥ 2` the limit is at least `log 2 > 0`, i.e. genuinely exponential growth.
-/

open AdjSum

open Finset Matrix Filter Topology

/-! ## A Fekete-type growth lemma -/



/-! ## The diagonal loop counts -/








/-! ## Existence of the dominant growth rate -/




open AdjSum in
theorem solution(c : ℝ) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) * c / (n + 1)) atTop (𝓝 c) := by
  have h : ∀ n : ℕ, (n : ℝ) * c / (n + 1) = c - c * (1 / ((n : ℝ) + 1)) := by
    intro n
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  simp only [h]
  have h0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Filter.Tendsto (fun n : ℕ => c * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using h0.const_mul c
  simpa using (tendsto_const_nhds (x := c) (f := (atTop : Filter ℕ))).sub h2
