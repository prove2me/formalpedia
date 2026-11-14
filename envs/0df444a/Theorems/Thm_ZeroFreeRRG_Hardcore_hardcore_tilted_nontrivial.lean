-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_tilted_nontrivial
-- name    : ZeroFreeRRG.Hardcore.hardcore_tilted_nontrivial
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:43:55.242736+00:00
-- url     : https://prove2.me/theorems/89bfacd2-9de2-4b51-885b-558befd74de9
-- title:
--   Nontriviality survives the hardcore tilt
-- statement:
--   Let $\eta$ be a measure supported on $[-1,1]$ that is not almost surely concentrated at zero, and let $0\leq\theta<1$. After tilting by $1+\theta h$ and mapping $h$ to $(1-h)/(1+\theta h)$, the resulting measure is not the point mass at $1$.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 4.17 proof, equation (25), pp. 29–31.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

theorem ZeroFreeRRG.Hardcore.hardcore_tilted_nontrivial (η : Measure ℝ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hb : ∀ᵐ h ∂η, -1 ≤ h ∧ h ≤ 1)
    (hn : ¬ (∀ᵐ h ∂η, h = 0)) :
    Measure.map (fun h : ℝ => (1-h)/(1+θ*h))
      (η.withDensity (fun h : ℝ => ENNReal.ofReal (1+θ*h))) ≠ Measure.dirac 1 := by sorry
