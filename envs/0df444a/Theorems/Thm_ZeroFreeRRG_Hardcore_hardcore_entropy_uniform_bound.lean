-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_entropy_uniform_bound
-- name    : ZeroFreeRRG.Hardcore.hardcore_entropy_uniform_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:49:04.927191+00:00
-- url     : https://prove2.me/theorems/496833b0-e1cc-4e5d-b0fb-cd0d63587865
-- title:
--   Uniform bounds for hardcore vertex entropy and its derivative
-- statement:
--   For fixed finite dimension $d$ and $T<1$, consider $0\le t\le T$ and messages $h_i\in[-1,1]$. Both the hardcore vertex entropy $V_t\log V_t$ and its pointwise derivative are uniformly bounded, where $$V_t=\frac{\prod_i(1+t h_i)+t\prod_i(1-h_i)}{1+t}.$$ The derivative is displayed explicitly in the formal statement. The bound is used to justify differentiation under an expectation.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, equation (25), pp. 29–31.

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators
open Set

theorem ZeroFreeRRG.Hardcore.hardcore_entropy_uniform_bound (d : ℕ) (T : ℝ) (hT : T < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (t : ℝ) (h : Fin d → ℝ),
      0 ≤ t → t ≤ T → (∀ i, -1 ≤ h i ∧ h i ≤ 1) →
      let V := ((∏ i, (1+t*h i)) + t*(∏ i, (1-h i)))/(1+t)
      let D := ((1+t)*(∑ i, (∏ j ∈ Finset.univ.erase i, (1+t*h j))*h i) +
        (∏ i, (1-h i)) - ∏ i, (1+t*h i)) / (1+t)^2
      ‖V * Real.log V‖ ≤ B ∧ ‖D * (Real.log V + 1)‖ ≤ B := by sorry
