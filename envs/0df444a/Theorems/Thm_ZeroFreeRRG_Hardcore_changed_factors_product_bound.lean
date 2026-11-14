-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_changed_factors_product_bound
-- name    : ZeroFreeRRG.Hardcore.changed_factors_product_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:12:43.433951+00:00
-- url     : https://prove2.me/theorems/83055380-8e1d-4418-91bd-4baec69db102
-- title:
--   Product comparison from changed factors
-- statement:
--   If two finite products of nonnegative old factors agree outside E and each changed factor is at most C times the corresponding new factor, then the old product is at most C to the power of the number of changed factors times the new product.
-- source:
--   Chunyang Wang et al., Zero-freeness for random regular graphs up to the replica symmetry breaking threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Appendix E.3, proof of Lemma 4.20, Step 1 (supporting argument).

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.changed_factors_product_bound {I : Type*} [DecidableEq I] (T E : Finset I) (x y : I → ℝ) (C : ℝ)
    (hx : ∀ i ∈ T, 0 ≤ x i)
    (hchanged : ∀ i ∈ T, i ∈ E → x i ≤ C * y i)
    (hunchanged : ∀ i ∈ T, i ∉ E → x i = y i) :
    (∏ i ∈ T, x i) ≤ C ^ (T.filter (· ∈ E)).card * ∏ i ∈ T, y i := by sorry
