-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_log_product_strict_mixed_difference
-- name    : ZeroFreeRRG.Hardcore.log_product_strict_mixed_difference
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:24:27.215241+00:00
-- url     : https://prove2.me/theorems/cf7fdb5b-bf74-402a-8cc1-7485f216edaf
-- title:
--   Strict mixed difference for the log-product potential
-- statement:
--   Let $x_a\le y_a$ be nonnegative on a finite set, with strict inequalities at distinct indices $i,j$, and let $\theta>0$. If every other $x_a$ is strictly positive, then the mixed difference of $\log(1+\theta\prod_a z_a)$ between $x$ and the two-coordinate increase is strictly positive. This is the positive-probability strictness step in the hardcore Bethe comparison.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed p. 30.

import Mathlib
open scoped BigOperators

namespace ZeroFreeRRG.Hardcore
theorem log_product_strict_mixed_difference {ι : Type} [Fintype ι] [DecidableEq ι] (θ : ℝ) (hθ : 0 < θ)
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i)
    (i j : ι) (hij : i ≠ j) (hi : x i < y i) (hj : x j < y j)
    (hrest : ∀ a, a ≠ i → a ≠ j → 0 < x a) :
    Real.log (1+θ*∏ a, (if a ∈ ({i,j} : Finset ι) then y a else x a)) +
      Real.log (1+θ*∏ a, x a) >
    Real.log (1+θ*∏ a, (if a = i then y a else x a)) +
      Real.log (1+θ*∏ a, (if a = j then y a else x a)) := by sorry
end ZeroFreeRRG.Hardcore
