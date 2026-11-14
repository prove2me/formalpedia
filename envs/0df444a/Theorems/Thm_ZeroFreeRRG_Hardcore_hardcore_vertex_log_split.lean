-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_vertex_log_split
-- name    : ZeroFreeRRG.Hardcore.hardcore_vertex_log_split
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:10:39.148044+00:00
-- url     : https://prove2.me/theorems/c97c5700-d892-4f6e-9bd0-981366267ba7
-- title:
--   Hardcore vertex logarithm decomposition
-- statement:
--   For $0\le\theta<1$ and messages $h_i\in[-1,1]$, write $P=\prod_i(1+\theta h_i)$, $Q=\prod_i(1-h_i)$ and $W_i=(1-h_i)/(1+\theta h_i)$. The vertex weight satisfies $$\log\frac{P+\theta Q}{1+\theta}=\sum_i\log(1+\theta h_i)+\log(1+\theta\prod_iW_i)-\log(1+\theta).$$
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, pp. 29–31.

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.hardcore_vertex_log_split (d : ℕ) (h : Fin d → ℝ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hb : ∀ i, -1 ≤ h i ∧ h i ≤ 1) :
    let P := ∏ i, (1+θ*h i)
    let Q := ∏ i, (1-h i)
    let W := fun i => (1-h i)/(1+θ*h i)
    Real.log ((P+θ*Q)/(1+θ)) =
      (∑ i, Real.log (1+θ*h i)) + Real.log (1+θ*∏ i, W i) - Real.log (1+θ) := by sorry
