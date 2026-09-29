-- Prove2me | solution 1 for EulerMascheroniInformationBridge.gammaTerm_partial_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:31:56.785157+00:00
-- url     : https://prove2.me/submissions/f64aa00a-a490-4e4c-9626-dcf9168ffdc5

-- Sol generated from Novelty/EulerMascheroniInformationBridge.lean
import Mathlib
import Definitions.Def_Novelty_EulerMascheroniInformationBridge

/-!
# Euler–Mascheroni constant as accumulated information divergence

This file connects analytic number theory with information theory.  For positive
rates `λ` and `μ`, the Kullback–Leibler divergence from an exponential law of rate
`λ` to one of rate `μ` has the closed form

`log (λ / μ) + μ / λ - 1`.

At the consecutive integer rates `λ = k+1`, `μ = k+2`, this is exactly the
`k`-th nonnegative summand in the classical series for the Euler–Mascheroni
constant.  Consequently, `γ` is the accumulated KL divergence along the chain
of exponential distributions with rates `1, 2, 3, ...`.
-/

open Real Filter Finset Topology

open EulerMascheroniInformationBridge



lemma harmonic_cast (n : ℕ) :
    (harmonic n : ℝ) = ∑ k ∈ range n, 1 / (k + 1 : ℝ) := by
  rw [harmonic]
  push_cast
  simp [one_div]

lemma sum_log_telescope (n : ℕ) :
    ∑ k ∈ range n, Real.log ((k + 2) / (k + 1) : ℝ) = Real.log (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, ← Real.log_mul (by positivity) (by positivity)]
    congr 1
    push_cast
    field_simp
    ring











open EulerMascheroniInformationBridge in
theorem solution(n : ℕ) :
    ∑ k ∈ range n, gammaTerm k = Real.eulerMascheroniSeq n := by
  unfold gammaTerm Real.eulerMascheroniSeq
  rw [Finset.sum_sub_distrib, sum_log_telescope, ← harmonic_cast]
