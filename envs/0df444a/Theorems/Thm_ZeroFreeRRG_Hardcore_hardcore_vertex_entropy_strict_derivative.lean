-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_vertex_entropy_strict_derivative
-- name    : ZeroFreeRRG.Hardcore.hardcore_vertex_entropy_strict_derivative
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:12:22.390874+00:00
-- url     : https://prove2.me/theorems/17fe5ce6-ac19-44d6-8793-2a9a0be9307a
-- title:
--   Strict increase of the hardcore vertex entropy contribution
-- statement:
--   Let $d\ge2$, and let $\eta$ be a mean-zero probability law supported on $[-1,1]$ that is not concentrated at zero. For independent messages $h_1,\ldots,h_d\sim\eta$ and $0<\theta<1$, set $$V_\theta=\frac{\prod_i(1+\theta h_i)+\theta\prod_i(1-h_i)}{1+\theta},\qquad F(\theta)=\mathbb E[V_\theta\log V_\theta].$$ Then $F′(\theta)>0$. This is the strict vertex-entropy monotonicity step in the hardcore parameter comparison.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, equation (25), pp. 29–31.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.hardcore_vertex_entropy_strict_derivative (d : ℕ) (hd : 2 ≤ d) (η : Measure ℝ) [IsProbabilityMeasure η]
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hb : ∀ᵐ h ∂η, -1 ≤ h ∧ h ≤ 1)
    (hint : Integrable (fun h : ℝ => h) η)
    (hmean : (∫ h : ℝ, h ∂η) = 0) (hn : ¬(∀ᵐ h ∂η, h=0)) :
    0 < deriv (fun t : ℝ => ∫ hs : Fin d → ℝ,
      let V := ((∏ i, (1+t*hs i)) + t*(∏ i, (1-hs i)))/(1+t)
      V * Real.log V ∂(Measure.pi fun _ : Fin d => η)) θ := by sorry
