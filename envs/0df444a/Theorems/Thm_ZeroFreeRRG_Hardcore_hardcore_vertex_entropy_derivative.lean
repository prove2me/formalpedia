-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_vertex_entropy_derivative
-- name    : ZeroFreeRRG.Hardcore.hardcore_vertex_entropy_derivative
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:47:41.785795+00:00
-- url     : https://prove2.me/theorems/8065ffc0-535e-43b8-9316-af63822686b2
-- title:
--   Pointwise derivative of the hardcore vertex entropy
-- statement:
--   Fix finitely many real messages $h_i$ and a real parameter $\theta$. Define $$V_\theta=\frac{\prod_i(1+\theta h_i)+\theta\prod_i(1-h_i)}{1+\theta}.$$ If $1+\theta$ and $V_\theta$ are nonzero, the derivative of $V_\theta\log V_\theta$ exists and equals $(1+\log V_\theta)$ times the explicit derivative of $V_\theta$ displayed in the formal statement. This is the pointwise ingredient for differentiating the hardcore vertex contribution.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, equation (25), pp. 29–31.

import Mathlib
set_option autoImplicit false
open scoped BigOperators

theorem ZeroFreeRRG.Hardcore.hardcore_vertex_entropy_derivative {ι : Type} [Fintype ι] [DecidableEq ι] (h : ι → ℝ) (θ : ℝ)
    (hden : 1+θ ≠ 0)
    (hV : ((∏ i, (1+θ*h i)) + θ*(∏ i, (1-h i)))/(1+θ) ≠ 0) :
    HasDerivAt
      (fun t : ℝ => let V := ((∏ i, (1+t*h i)) + t*(∏ i, (1-h i)))/(1+t)
        V * Real.log V)
      ((((1+θ)*(∑ i, (∏ j ∈ Finset.univ.erase i, (1+θ*h j))*h i) +
          (∏ i, (1-h i)) - ∏ i, (1+θ*h i)) / (1+θ)^2) *
        (Real.log (((∏ i, (1+θ*h i)) + θ*(∏ i, (1-h i)))/(1+θ)) + 1)) θ := by sorry
