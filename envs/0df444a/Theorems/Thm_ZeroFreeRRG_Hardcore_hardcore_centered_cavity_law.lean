-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_centered_cavity_law
-- name    : ZeroFreeRRG.Hardcore.hardcore_centered_cavity_law
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:17:06.008388+00:00
-- url     : https://prove2.me/theorems/d2a70bde-4851-4da6-8689-3d9f3f526216
-- title:
--   Nontrivial hardcore cavity laws give centered message laws
-- statement:
--   Let $0<\alpha<1/2$ and let $\nu$ be a hardcore cavity law with barycenter $(1-\alpha,\alpha)$, other than its point mass. The image under $h=(\mu_1-\alpha)/(1-\alpha)$ is a probability law supported on $[-1,1]$ with mean zero, and it is not concentrated at zero.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, equation (25), pp. 29–31.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical

theorem ZeroFreeRRG.Hardcore.hardcore_centered_cavity_law (α : ℝ) (ha : 0 < α) (ha1 : α < 1/2)
    (ν : ProbabilityMeasure (Fin 2 → ℝ)) (hν : ν ∈ cavityLaws .hardcore α)
    (hne : ν ≠ diracPi .hardcore α) :
    let η := Measure.map (fun x : Fin 2 → ℝ => (x 1-α)/(1-α)) (ν : Measure (Fin 2 → ℝ))
    IsProbabilityMeasure η ∧ (∀ᵐ h ∂η, -1 ≤ h ∧ h ≤ 1) ∧
      Integrable (fun h : ℝ => h) η ∧ (∫ h : ℝ, h ∂η) = 0 ∧
      ¬(∀ᵐ h ∂η, h=0) := by sorry
