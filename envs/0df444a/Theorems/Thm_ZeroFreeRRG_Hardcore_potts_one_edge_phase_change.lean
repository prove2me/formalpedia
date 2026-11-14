-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_one_edge_phase_change
-- name    : ZeroFreeRRG.Hardcore.potts_one_edge_phase_change
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:11:29.996414+00:00
-- url     : https://prove2.me/theorems/386f6cce-75be-4eed-8cbe-63cc34631074
-- title:
--   Phase change when one set of Potts coefficients changes
-- statement:
--   Suppose a finite complex sum is sector controlled by the factor $7/8$, and each original and replacement coefficient lies on the segment from $1$ to $\beta$. If $d\ge3$ and $|\beta-1|<0.35/d$, replacing the coefficients preserves nonvanishing and changes the normalized phase by at most $(25/23)|\beta-1|/((7/8)(1-|\beta-1|))$.
-- source:
--   Auxiliary phase bound for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.potts_one_edge_phase_change {ι : Type} (S : Finset ι) (z a b : ι → ℂ) (d : ℕ) (hd : 3 ≤ d)
    (β : ℂ) (hβ : ‖β-1‖ < 0.35/(d:ℝ))
    (ha : ∀ i ∈ S, ∃ t : ℝ, t ∈ Icc 0 1 ∧ a i = 1+(t:ℂ)*(β-1))
    (hb : ∀ i ∈ S, ∃ t : ℝ, t ∈ Icc 0 1 ∧ b i = 1+(t:ℂ)*(β-1))
    (hsum : (7/8:ℝ)*(∑ i ∈ S, ‖z i‖) ≤ ‖∑ i ∈ S, z i‖)
    (hne : (∑ i ∈ S, z i) ≠ 0) :
    let Z := ∑ i ∈ S, z i
    let Z' := ∑ i ∈ S, (b i/a i)*z i
    Z' ≠ 0 ∧ ‖Z/(‖Z‖:ℂ)-Z'/(‖Z'‖:ℂ)‖ ≤
      (25/23)*(‖β-1‖/((7/8:ℝ)*(1-‖β-1‖))) := by sorry
