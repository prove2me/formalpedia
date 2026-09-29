-- Prove2me | solution 1 for DickmanFinite.one_lt_dickmanLead
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:33:00.547986+00:00
-- url     : https://prove2.me/submissions/6ef63da0-e1ee-4556-971c-9f7f48d99dad

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





open DickmanFinite in
theorem solution{u : ℝ} (hu1 : 1 < u) (hu2 : u ≤ 2) : 1 < dickmanLead u := by
  have hlogpos : 0 < Real.log u := Real.log_pos hu1
  have hlogle : Real.log u ≤ Real.log 2 :=
    Real.log_le_log (by linarith) hu2
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  -- `log log u ≤ log u - 1 < 0`
  have hll : Real.log (Real.log u) ≤ Real.log u - 1 :=
    Real.log_le_sub_one_of_pos hlogpos
  have hexp : 0 < -u * (Real.log u + Real.log (Real.log u) - 1) := by
    have hsum : Real.log u + Real.log (Real.log u) - 1 < 0 := by linarith
    nlinarith
  calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
    _ < _ := Real.exp_lt_exp.2 hexp
