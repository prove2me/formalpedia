-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_entropy_integral_derivative
-- name    : ZeroFreeRRG.Hardcore.hardcore_entropy_integral_derivative
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:50:36.08388+00:00
-- url     : https://prove2.me/theorems/6a37f9ca-38b6-4f5d-99b9-ac8b138926a9
-- title:
--   Differentiation under the hardcore vertex-entropy expectation
-- statement:
--   Let $\eta$ be any probability measure supported on $[-1,1]$, and let $d$ independent messages have law $\eta$. For $0<\theta<1$, the expected hardcore vertex entropy $$F(\theta)=\mathbb E[V_\theta\log V_\theta]$$ is differentiable, and its derivative is the expectation of the pointwise derivative displayed in the formal statement. Here $V_\theta=(\prod_i(1+\theta h_i)+\theta\prod_i(1-h_i))/(1+\theta)$.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, equation (25), pp. 29–31.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Classical BigOperators Topology

theorem ZeroFreeRRG.Hardcore.hardcore_entropy_integral_derivative (d : ℕ) (η : Measure ℝ) [IsProbabilityMeasure η]
    (hb : ∀ᵐ h ∂η, -1 ≤ h ∧ h ≤ 1) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    let μ := Measure.pi (fun _ : Fin d => η)
    let V := fun (t : ℝ) (h : Fin d → ℝ) =>
      ((∏ i, (1+t*h i)) + t*(∏ i, (1-h i)))/(1+t)
    let D := fun (t : ℝ) (h : Fin d → ℝ) =>
      ((1+t)*(∑ i, (∏ j ∈ Finset.univ.erase i, (1+t*h j))*h i) +
        (∏ i, (1-h i)) - ∏ i, (1+t*h i)) / (1+t)^2
    HasDerivAt (fun t => ∫ h, V t h * Real.log (V t h) ∂μ)
      (∫ h, D θ h * (Real.log (V θ h) + 1) ∂μ) θ := by sorry
