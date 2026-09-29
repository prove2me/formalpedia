-- Prove2me | solution 1 for EulerMascheroniInformationBridge.hasSum_gammaTerm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:34:28.036842+00:00
-- url     : https://prove2.me/submissions/746c6ff2-04b0-4ee0-8d4d-a9b88c0b8983

-- Sol generated from Novelty/EulerMascheroniInformationBridge.lean
import Mathlib
import Definitions.Def_Novelty_EulerMascheroniInformationBridge
import Theorems.Thm_EulerMascheroniInformationBridge_gammaTerm_partial_sum

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


lemma gammaTerm_nonneg (k : ℕ) : 0 ≤ gammaTerm k := by
  have hx : (0 : ℝ) < (k + 2) / (k + 1) := by positivity
  have h := Real.log_le_sub_one_of_pos hx
  have hsub : ((k : ℝ) + 2) / (k + 1) - 1 = 1 / (k + 1) := by
    field_simp
    ring
  rw [hsub] at h
  simpa [gammaTerm] using sub_nonneg.mpr h













open EulerMascheroniInformationBridge in
theorem solution: HasSum gammaTerm Real.eulerMascheroniConstant := by
  refine (hasSum_iff_tendsto_nat_of_nonneg gammaTerm_nonneg _).mpr ?_
  simp_rw [gammaTerm_partial_sum]
  exact Real.tendsto_eulerMascheroniSeq
