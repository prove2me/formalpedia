-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_bounded_fiber_weighted_sum
-- name    : ZeroFreeRRG.Hardcore.bounded_fiber_weighted_sum
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:11:01.33123+00:00
-- url     : https://prove2.me/theorems/9406aca5-1272-4e6b-8b5b-77088ba7d747
-- title:
--   Weighted sum comparison under a bounded-fiber map
-- statement:
--   Suppose a map from a finite set T into H has at most B preimages per point, and the weight at each point of T is at most C times the weight at its image. If the weights on H and C are nonnegative, the sum over T is at most BC times the sum over H.
-- source:
--   Chunyang Wang et al., Zero-freeness for random regular graphs up to the replica symmetry breaking threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Appendix E.3, proof of Lemma 4.20, Step 1 (supporting argument).

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.bounded_fiber_weighted_sum {X : Type*} [DecidableEq X]
    (T H : Finset X) (F : X → X) (w : X → ℝ) (B : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hw : ∀ y ∈ H, 0 ≤ w y)
    (hmap : ∀ x ∈ T, F x ∈ H)
    (hfiber : ∀ y ∈ H, (T.filter (fun x => F x = y)).card ≤ B)
    (hbound : ∀ x ∈ T, w x ≤ C * w (F x)) :
    (∑ x ∈ T, w x) ≤ (B : ℝ) * C * ∑ y ∈ H, w y := by sorry
