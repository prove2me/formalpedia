-- Prove2me | solution 1 for EulerMascheroniInformationBridge.gammaTerm_le_rational
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:57:34.72548+00:00
-- url     : https://prove2.me/submissions/d726a448-ac7b-4f19-b726-5340c5b1face

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
theorem solution(k : ℕ) :
    gammaTerm k ≤ 1 / ((k + 1 : ℝ) * (2 * k + 3)) := by
  unfold gammaTerm
  -- Need: 1/(k+1) - log((k+2)/(k+1)) ≤ 1/((k+1)(2k+3))
  -- Equiv: log((k+2)/(k+1)) ≥ 1/(k+1) - 1/((k+1)(2k+3)) = 2/(2k+3)
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have hk2 : (0 : ℝ) < k + 2 := by positivity
  have hk23 : (0 : ℝ) < 2 * k + 3 := by positivity
  have h1 : (k + 2 : ℝ) / (k + 1) = 1 + 1 / (k + 1) := by field_simp; ring
  -- Inequality: log(1 + x) ≥ 2x/(2+x) for x > 0
  have x_pos : (0 : ℝ) < 1 / (k + 1) := by positivity
  have log_bound : 2 / (2 * (k : ℝ) + 3) ≤ Real.log ((k + 2) / (k + 1)) := by
    rw [h1]
    have hx : (1 : ℝ) / (k + 1) = 1 / (k + 1) := rfl
    have h2x : 2 / (2 * (k : ℝ) + 3) = 2 * (1 / (k + 1)) / (2 + 1 / (k + 1)) := by
      field_simp
      ring
    rw [h2x]
    -- Prove: 2x/(2+x) ≤ log(1+x) for x > 0
    have padé_lower_bound : ∀ x : ℝ, 0 < x → 2 * x / (2 + x) ≤ Real.log (1 + x) := by
      intro x hx
      by_contra h_neg
      have h_cont : ContinuousOn (fun t => Real.log (1 + t) - 2 * t / (2 + t)) (Set.Icc 0 x) := by
        refine ContinuousOn.sub ?_ ?_
        · exact ContinuousOn.log (continuousOn_const.add continuousOn_id) (by intro t ht; linarith [ht.1])
        · exact (continuousOn_const.mul continuousOn_id).div (continuousOn_const.add continuousOn_id)
            (by intro t ht; linarith [ht.1])
      have h_diff : ∀ y ∈ Set.Ioo 0 x, DifferentiableAt ℝ (fun t => Real.log (1 + t) - 2 * t / (2 + t)) y := by
        intro y hy
        have hy0 : 0 < y := hy.1
        apply DifferentiableAt.sub
        · have h1y : (1 : ℝ) + y ≠ 0 := by linarith
          exact DifferentiableAt.log (differentiableAt_id.const_add _) h1y
        · have h2y : (2 : ℝ) + y ≠ 0 := by linarith
          exact ((differentiableAt_id.const_mul _).div (differentiableAt_id.const_add _) h2y)
      have hderiv_pos : ∀ y ∈ Set.Ioo 0 x, 0 < deriv (fun t => Real.log (1 + t) - 2 * t / (2 + t)) y := by
        intro y hy
        have hy0 : 0 < y := hy.1
        have h1 : (1 : ℝ) + y ≠ 0 := by linarith
        have h2 : (2 : ℝ) + y ≠ 0 := by linarith
        have key : deriv (fun t => Real.log (1 + t) - 2 * t / (2 + t)) y =
            (1 * (2 + y)^2 - (1 + y) * 4) / ((1 + y) * (2 + y)^2) := by
          have := HasDerivAt.sub (Real.hasDerivAt_log h1 |>.comp y (hasDerivAt_id' y |>.const_add 1))
            (HasDerivAt.div ((hasDerivAt_id' y |>.const_mul 2))
              (hasDerivAt_id' y |>.const_add 2) h2)
          convert this.deriv using 1
          field_simp
          ring
        rw [key]
        apply div_pos
        · nlinarith [sq_nonneg y]
        · apply mul_pos (by linarith) (sq_pos_of_pos (by linarith))
      have hf0 : (fun t => Real.log (1 + t) - 2 * t / (2 + t)) 0 = 0 := by simp
      have hf_x_neg : (fun t => Real.log (1 + t) - 2 * t / (2 + t)) x < 0 := by simpa [hf0] using h_neg
      obtain ⟨c, hc_mem, hc_eq⟩ := exists_deriv_eq_slope (fun t => Real.log (1 + t) - 2 * t / (2 + t)) hx
        h_cont (fun y hy => (h_diff y hy).differentiableWithinAt)
      have hderiv_eq : deriv (fun t => Real.log (1 + t) - 2 * t / (2 + t)) c =
          ((fun t => Real.log (1 + t) - 2 * t / (2 + t)) x - 0) / (x - 0) := by
        simpa [hf0] using hc_eq
      have hc_pos : 0 < deriv (fun t => Real.log (1 + t) - 2 * t / (2 + t)) c := hderiv_pos c hc_mem
      rw [hderiv_eq] at hc_pos
      simp only [sub_zero] at hc_pos
      have h_neg_div : (Real.log (1 + x) - 2 * x / (2 + x)) / x < 0 := by
        rw [div_lt_iff₀ hx]
        linarith [hf_x_neg]
      linarith
    exact padé_lower_bound _ x_pos
  have rhs_simp : 1 / ((k + 1 : ℝ)) - 1 / ((k + 1) * (2 * k + 3)) = 2 / (2 * (k : ℝ) + 3) := by
    field_simp
    ring
  linarith
