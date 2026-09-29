-- Prove2me | solution 1 for DickmanFinite.finiteCorrection_window
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:32:54.574087+00:00
-- url     : https://prove2.me/submissions/3e17dbc3-5c6f-4250-b3fc-0e8d5a3a5d5a

-- Sol generated from Shared/DickmanFiniteCorrection.lean
import Mathlib
import Definitions.Def_Shared_DickmanFiniteCorrection

/-!
# The Dickman leading term, its finite-size correction, and why it is slow

Context (experiment 465, paper 130).  Smoothness probabilities in the quadratic
sieve are modelled by the Dickman function `ρ(u)`, and in the asymptotic analysis
of subexponential factoring one replaces `ρ(u)` by its leading term

`L(u) = exp (-u (log u + log log u - 1))`.

The experiment measured, over `1.2 · 10^6` smoothness tests with
`N ∈ {2^32 .. 2^44}`, that

* the empirical smooth-density / `ρ(u)` ratio sits in `0.877 – 0.913` at every
  scale, **equally for the `x^2 - N` pool and for the size-matched random
  control**, and
* the discrepancy has the size of the finite-`x` correction
  `log log v / log v ≈ 17–20 %` for the value sizes involved, shrinking only
  logarithmically, and
* the leading term `L(u)` is a useless proxy for `ρ(u)` at reachable `u`.

This file proves the analytic facts behind those three statements.

Main results:

* `rhoTwo_lt_one`, `rhoTwo_pos` — the exact Dickman value on `(1,2]` is a
  genuine probability, `ρ(u) = 1 - log u ∈ (0,1)`.
* `one_lt_dickmanLead` — on `(1,2]` the leading term is `> 1`: it is not even a
  probability there, so it cannot approximate `ρ`.
* `dickmanLead_two_gt_nine_mul_rho` — quantitatively, at `u = 2` the leading term
  overshoots the true value by more than a factor `9`.
* `dickmanLead_lt_one_of_three_le` — the leading term only becomes admissible
  from `u ≥ 3` onwards (and, per the experiment, only becomes *accurate* near
  `u ≈ 14.75`).
* `finiteCorrection_antitoneOn` — the finite-size correction `log log v / log v`
  decreases, but only logarithmically.
* `finiteCorrection_tendsto_zero` — it does vanish: nothing blocks convergence.
* `finiteCorrection_window` — in the experimental window `e^12 ≤ v ≤ e^20` it
  lies in `[0.1, 0.25]`, bracketing the measured `17–20 %` deficit.
-/

open DickmanFinite

open Real Filter Topology



/-! ## `ρ` is a probability on `(1,2]`, the leading term is not -/










/-! ## The finite-size correction -/




/-! ### The experimental window -/

theorem exp_two_lt_twelve : Real.exp 2 < 12 := by
  have h := Real.exp_one_lt_d9
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith

theorem twenty_lt_exp_three : (20 : ℝ) < Real.exp 3 := by
  have h := Real.exp_one_gt_d9
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h3 : Real.exp 3 = Real.exp 1 * (Real.exp 1 * Real.exp 1) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  nlinarith



open DickmanFinite in
theorem solution{v : ℝ} (h1 : Real.exp 12 ≤ v) (h2 : v ≤ Real.exp 20) :
    0.1 ≤ finiteCorrection v ∧ finiteCorrection v ≤ 0.25 := by
  have hvpos : (0 : ℝ) < v := lt_of_lt_of_le (Real.exp_pos _) h1
  have hl1 : (12 : ℝ) ≤ Real.log v := by
    have := Real.log_le_log (Real.exp_pos 12) h1
    rwa [Real.log_exp] at this
  have hl2 : Real.log v ≤ 20 := by
    have := Real.log_le_log hvpos h2
    rwa [Real.log_exp] at this
  set t := Real.log v with ht
  have htpos : (0 : ℝ) < t := by linarith
  -- `2 ≤ log t ≤ 3`
  have hlow : (2 : ℝ) ≤ Real.log t := by
    have : Real.exp 2 ≤ t := le_trans exp_two_lt_twelve.le hl1
    calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ ≤ Real.log t := Real.log_le_log (Real.exp_pos 2) this
  have hhigh : Real.log t ≤ 3 := by
    have : t ≤ Real.exp 3 := le_trans hl2 twenty_lt_exp_three.le
    calc Real.log t ≤ Real.log (Real.exp 3) := Real.log_le_log htpos this
      _ = 3 := Real.log_exp 3
  constructor
  · rw [finiteCorrection, ← ht, le_div_iff₀ htpos]
    nlinarith
  · rw [finiteCorrection, ← ht, div_le_iff₀ htpos]
    nlinarith
