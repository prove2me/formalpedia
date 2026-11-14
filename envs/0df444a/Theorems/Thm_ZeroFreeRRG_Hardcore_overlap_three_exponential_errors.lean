-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_overlap_three_exponential_errors
-- name    : ZeroFreeRRG.Hardcore.overlap_three_exponential_errors
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:34:17.910193+00:00
-- url     : https://prove2.me/theorems/4d241a4c-21ce-463e-bca4-432c348f1c08
-- title:
--   Absorption of three exponential overlap errors
-- statement:
--   For nonnegative constants $A,B,C$ and positive rates $a,b,c$, there are $r>0$ and $N$ such that for every integer $n\ge N$, $$A e^{-an}+B e^{-bn}+C e^{-cn}\le e^{-rn}.$$ This absorbs the three error terms at the end of the planted-overlap estimate.
-- source:
--   Auxiliary estimate for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, pp. 39–40, proof of Lemma 5.6.

import Mathlib
set_option autoImplicit false

theorem ZeroFreeRRG.Hardcore.overlap_three_exponential_errors (A B C a b c : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ r : ℝ, 0 < r ∧ ∃ N : ℕ, ∀ n ≥ N,
      A * Real.exp (-a * n) + B * Real.exp (-b * n) + C * Real.exp (-c * n)
        ≤ Real.exp (-r * n) := by sorry
