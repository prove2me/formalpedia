-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_finite_factor_ratio_bound
-- name    : ZeroFreeRRG.Hardcore.finite_factor_ratio_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:12:41.227099+00:00
-- url     : https://prove2.me/theorems/a835620f-b560-4f85-8a07-3c36a5673d1f
-- title:
--   Finite-factor ratio bound
-- statement:
--   For any finite spin set, positive one-site weights, and arbitrary interaction weights, there is a constant C at least one that bounds every ratio of one-site weights and every ratio of interaction weights having a strictly positive denominator.
-- source:
--   Chunyang Wang et al., Zero-freeness for random regular graphs up to the replica symmetry breaking threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Appendix E.3, proof of Lemma 4.20, Step 1 (supporting argument).

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.finite_factor_ratio_bound {A : Type*} [Fintype A] (p : A → ℝ) (J : A → A → ℝ)
    (hp : ∀ a, 0 < p a) :
    ∃ C : ℝ, 1 ≤ C ∧ (∀ a b, p a ≤ C * p b) ∧
      (∀ a b c d, 0 < J c d → J a b ≤ C * J c d) := by sorry
