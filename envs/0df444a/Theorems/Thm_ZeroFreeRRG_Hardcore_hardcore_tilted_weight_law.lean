-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_tilted_weight_law
-- name    : ZeroFreeRRG.Hardcore.hardcore_tilted_weight_law
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:42:50.36821+00:00
-- url     : https://prove2.me/theorems/aec0ec0e-1cb9-472e-8087-08a018409b4a
-- title:
--   Tilted hardcore cavity weights have bounded mean-one law
-- statement:
--   Let $\eta$ be a probability law supported on $[-1,1]$ with mean zero, and let $0\leq\theta<1$. Tilt $\eta$ by the density $1+\theta h$ and map $h$ to $W=(1-h)/(1+\theta h)$. The image is a probability law supported on $[0,2/(1-\theta)]$ and $\mathbb E W=1$.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 4.17 proof, equation (25), pp. 29–31.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

theorem ZeroFreeRRG.Hardcore.hardcore_tilted_weight_law (η : Measure ℝ) [IsProbabilityMeasure η] (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hb : ∀ᵐ h ∂η, -1 ≤ h ∧ h ≤ 1)
    (hint : Integrable (fun h : ℝ => h) η)
    (hmean : (∫ h : ℝ, h ∂η) = 0) :
    let tilt := η.withDensity (fun h : ℝ => ENNReal.ofReal (1 + θ*h))
    let ν := Measure.map (fun h : ℝ => (1-h)/(1+θ*h)) tilt
    IsProbabilityMeasure ν ∧
      (∀ᵐ w ∂ν, 0 ≤ w ∧ w ≤ 2/(1-θ)) ∧
      Integrable (fun w : ℝ => w) ν ∧ (∫ w : ℝ, w ∂ν) = 1 := by sorry
