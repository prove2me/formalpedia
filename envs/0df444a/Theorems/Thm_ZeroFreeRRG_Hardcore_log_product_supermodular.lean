-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_log_product_supermodular
-- name    : ZeroFreeRRG.Hardcore.log_product_supermodular
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:14:19.574743+00:00
-- url     : https://prove2.me/theorems/c08f88aa-d380-432d-b0fc-0309e85368b8
-- title:
--   Supermodularity of the log-product term
-- statement:
--   Let $t,x,x′,y,y′$ be nonnegative real numbers with $x\le x′$ and $y\le y′$. Then the sum of $\log(1+t x′y′)$ and $\log(1+txy)$ is at least the sum of $\log(1+t x′y)$ and $\log(1+txy′)$. The inequality is strict if $t>0$, $x<x′$, and $y<y′$. This is the two-coordinate supermodularity used in the hardcore monotonicity argument.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed p. 30.

import Mathlib

namespace ZeroFreeRRG.Hardcore
theorem log_product_supermodular (t x x' y y' : ℝ) (ht : 0 ≤ t)
    (hx : 0 ≤ x) (hxx : x ≤ x') (hy : 0 ≤ y) (hyy : y ≤ y') :
    Real.log (1+t*x'*y') + Real.log (1+t*x*y) ≥
      Real.log (1+t*x'*y) + Real.log (1+t*x*y') ∧
    (0 < t → x < x' → y < y' →
      Real.log (1+t*x'*y') + Real.log (1+t*x*y) >
        Real.log (1+t*x'*y) + Real.log (1+t*x*y')) := by sorry
end ZeroFreeRRG.Hardcore
