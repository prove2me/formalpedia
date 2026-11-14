-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_log_product_set_supermodular
-- name    : ZeroFreeRRG.Hardcore.log_product_set_supermodular
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:12:10.823018+00:00
-- url     : https://prove2.me/theorems/d9d97d31-d432-4da0-88d2-f7f6a08f9c8f
-- title:
--   Supermodularity of the finite log-product potential
-- statement:
--   Let $x_i\le y_i$ be nonnegative for every element of a finite index set, and let $\theta\ge0$. For a subset $S$, form the vector taking $y_i$ on $S$ and $x_i$ elsewhere, and set $v(S)=\log(1+\theta\prod_i z_i)$. Then $v$ has nonnegative mixed differences when two distinct elements outside $S$ are inserted. This is the finite-coordinate supermodularity required in the hardcore comparison.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed p. 30.

import Mathlib
open scoped BigOperators

namespace ZeroFreeRRG.Hardcore
theorem log_product_set_supermodular {ι : Type} [Fintype ι] [DecidableEq ι] (θ : ℝ) (hθ : 0 ≤ θ)
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i)
    (S : Finset ι) (i j : ι) (hi : i ∉ S) (hj : j ∉ S) (hij : i ≠ j) :
    Real.log (1+θ*∏ a, (if a ∈ insert i (insert j S) then y a else x a)) +
      Real.log (1+θ*∏ a, (if a ∈ S then y a else x a)) ≥
    Real.log (1+θ*∏ a, (if a ∈ insert i S then y a else x a)) +
      Real.log (1+θ*∏ a, (if a ∈ insert j S then y a else x a)) := by sorry
end ZeroFreeRRG.Hardcore
