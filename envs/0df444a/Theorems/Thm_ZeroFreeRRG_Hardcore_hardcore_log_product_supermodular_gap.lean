-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_log_product_supermodular_gap
-- name    : ZeroFreeRRG.Hardcore.hardcore_log_product_supermodular_gap
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:26:00.773358+00:00
-- url     : https://prove2.me/theorems/3989fa21-7577-4629-876f-d459fb88ed6f
-- title:
--   Nonnegative and strictly positive hardcore log-product gap
-- statement:
--   For nonnegative vectors $x\le y$ on a finite set and $\theta\ge0$, let $g(S)=\log(1+\theta\prod_i z_i)$ with $z_i=y_i$ on $S$ and $x_i$ elsewhere. Then $g(U)-g(\varnothing)-\sum_i(g(\{i\})-g(\varnothing))\ge0$. It is strictly positive when $\theta>0$, two coordinates increase strictly, and all other coordinates of $x$ are positive. This is the pointwise inequality used after the size-bias coupling in the hardcore comparison.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed p. 30.

import Mathlib
open scoped BigOperators

namespace ZeroFreeRRG.Hardcore
theorem hardcore_log_product_supermodular_gap {ι : Type} [Fintype ι] [DecidableEq ι] (θ : ℝ) (hθ : 0 ≤ θ)
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) :
    let g := fun S : Finset ι => Real.log (1+θ*∏ a, if a ∈ S then y a else x a)
    g Finset.univ ≥ g ∅ + ∑ i, (g {i}-g ∅) ∧
    (0 < θ → ∀ i j, i ≠ j → x i < y i → x j < y j →
      (∀ a, a ≠ i → a ≠ j → 0 < x a) →
      g Finset.univ > g ∅ + ∑ i, (g {i}-g ∅)) := by sorry
end ZeroFreeRRG.Hardcore
