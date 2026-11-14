-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_vertex_factor_derivative
-- name    : ZeroFreeRRG.Hardcore.hardcore_vertex_factor_derivative
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:35:22.171946+00:00
-- url     : https://prove2.me/theorems/5f7fcbc6-defd-45ff-b31e-923a638bb9d9
-- title:
--   Derivative of the centered hardcore vertex factor
-- statement:
--   For a finite family $(h_i)$ and $1+\theta\ne0$, consider $V(\theta)=[\prod_i(1+\theta h_i)+\theta\prod_i(1-h_i)]/(1+\theta)$. Its derivative is $[(1+\theta)\sum_i h_i\prod_{j\ne i}(1+\theta h_j)+\prod_i(1-h_i)-\prod_i(1+\theta h_i)]/(1+\theta)^2$. This is the pointwise differentiation step for the hardcore Bethe comparison.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed pp. 29–30, equation (25).

import Mathlib
open scoped BigOperators

namespace ZeroFreeRRG.Hardcore
theorem hardcore_vertex_factor_derivative {ι : Type} [Fintype ι] [DecidableEq ι] (h : ι → ℝ) (θ : ℝ)
    (hden : 1+θ ≠ 0) :
    HasDerivAt (fun t : ℝ => ((∏ i, (1+t*h i)) + t*(∏ i, (1-h i)))/(1+t))
      (((1+θ)*(∑ i, (∏ j ∈ Finset.univ.erase i, (1+θ*h j))*h i) +
          (∏ i, (1-h i)) - ∏ i, (1+θ*h i)) / (1+θ)^2) θ := by sorry
end ZeroFreeRRG.Hardcore
