-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_size_biased_log_jensen
-- name    : ZeroFreeRRG.Hardcore.size_biased_log_jensen
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:52:39.859951+00:00
-- url     : https://prove2.me/theorems/8017112b-7028-4363-90f3-f76e1b0ae8d3
-- title:
--   Logarithmic Jensen inequality under finite size bias
-- statement:
--   For any nonempty finite collection of positive values, the average of their logarithms under size-biased weights is at least the logarithm of their ordinary arithmetic mean.
-- source:
--   Auxiliary convexity inequality for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 31 and Appendix E.3, Lemma 4.20.

import Mathlib
set_option autoImplicit false
open Set
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.size_biased_log_jensen {I : Type} [Fintype I] [Nonempty I] (x : I → ℝ) (hx : ∀ i, 0 < x i) :
    Real.log ((∑ i, x i) / (Fintype.card I : ℝ)) ≤
      (∑ i, x i * Real.log (x i)) / (∑ i, x i) := by sorry
