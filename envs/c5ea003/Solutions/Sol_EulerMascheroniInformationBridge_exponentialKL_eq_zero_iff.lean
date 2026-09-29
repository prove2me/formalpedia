-- Prove2me | solution 1 for EulerMascheroniInformationBridge.exponentialKL_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:57:34.070364+00:00
-- url     : https://prove2.me/submissions/79ef4148-caad-47c9-bb70-0bfc5dd988a6

-- Sol generated from Shared/EulerMascheroniInformationBridge.lean
import Mathlib
import Definitions.Def_Shared_EulerMascheroniInformationBridge

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
























open EulerMascheroniInformationBridge in
theorem solution{rate₁ rate₂ : ℝ}
    (h₁ : 0 < rate₁) (h₂ : 0 < rate₂) :
    exponentialKL rate₁ rate₂ = 0 ↔ rate₁ = rate₂ := by
  constructor
  · intro heq
    unfold exponentialKL at heq
    have hr : 0 < rate₂ / rate₁ := div_pos h₂ h₁
    by_contra hne
    have hne' : rate₂ / rate₁ ≠ 1 := by
      intro h
      field_simp at h
      exact hne h.symm
    have hlog_strict := Real.log_lt_sub_one_of_pos hr hne'
    have hlog_eq : Real.log (rate₁ / rate₂) = -Real.log (rate₂ / rate₁) := by
      rw [← Real.log_inv, inv_div]
    linarith
  · intro heq
    rw [heq]
    unfold exponentialKL
    simp [div_self h₂.ne']
