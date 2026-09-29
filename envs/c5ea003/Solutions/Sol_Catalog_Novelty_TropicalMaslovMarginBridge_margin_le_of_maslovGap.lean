-- Prove2me | solution 1 for Catalog.Novelty.TropicalMaslovMarginBridge.margin_le_of_maslovGap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:30:49.456185+00:00
-- url     : https://prove2.me/submissions/e3ac5029-6a5d-4264-a99a-10d2b4191362

-- Sol generated from Novelty/TropicalMaslovMarginBridge.lean
import Mathlib
import Definitions.Def_Novelty_KVDecisionDissociation
import Definitions.Def_Novelty_TropicalMaslovMarginBridge
import Theorems.Thm_Catalog_Novelty_TropicalMaslovMarginBridge_maslovGap_le_of_margin

/-!
# The Maslov gap ↔ margin bridge (NET-50 ⋈ NET-51)

NET-50 measured, for the same transformer stack, a *tropical* quantity: the
**Maslov gap** `logsumexp(x) - max(x)` of the pre-softmax attention scores.  Its
median is close to `0` for most layers ("near-tropical": softmax behaves like a
max) and jumps to `2.5–2.7` exactly in the tail layers L22/L23.  NET-51 measured a
*functional* quantity on the same layers: top-1 decision agreement between two
fine-tunes, which collapses in exactly those layers.

This file proves that these are two views of one inequality.  Writing
`lse x = log ∑ exp (x i)` and `maslovGap x i = lse x - x i`:

* `maslovGap_nonneg`, `maslovGap_le_log_card` — the gap lives in `[0, log n]`,
  the tropical/Maslov dequantization window.
* `maslovGap_le_of_margin` — a margin `m` at the top forces a *small* gap:
  `gap ≤ log (1 + (n-1) e^{-m})`.  Near-tropical behaviour is exactly the regime
  of large margins.
* `margin_le_of_maslovGap` and `margin_le_of_maslovGap_simple` — the converse:
  a measured gap `g ≥ 1` caps the margin by `log (n-1) + log 2 - g`.  **Every nat
  of Maslov gap costs a nat of margin.**
* `exists_small_margin_of_maslovGap` + `flip_of_small_margin` — and a small margin
  is precisely a flippable decision: the far-from-tropical tail admits a
  perturbation of half the margin that changes the model's choice.
* `far_from_tropical_is_fragile` — the composite statement: a large Maslov gap
  yields an explicit small perturbation that destroys the top-1 decision.  This
  is the formal content of the NET-50/NET-51 convergence.
-/

open Catalog.Novelty.TropicalMaslovMarginBridge

open Finset Catalog.Novelty.KVDecisionDissociation

variable {n : ℕ}







/-! ### Margin ⟹ small gap (near-tropical) -/


/-! ### Large gap ⟹ small margin (far from tropical) -/



/-! ### Small margin ⟹ flippable decision -/





open Catalog.Novelty.TropicalMaslovMarginBridge in
theorem solution(x : Fin n → ℝ) (i : Fin n) (m g : ℝ)
    (hm : ∀ j, j ≠ i → m ≤ x i - x j) (hg : 0 < g) (hgap : g ≤ maslovGap x i)
    (hn : 2 ≤ n) :
    m ≤ Real.log ((n : ℝ) - 1) - Real.log (Real.exp g - 1) := by
  have hn1 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hupper := maslovGap_le_of_margin x i m hm
  have hpos : (0 : ℝ) < 1 + ((n : ℝ) - 1) * Real.exp (-m) := by
    have := Real.exp_pos (-m); nlinarith
  have hglog : g ≤ Real.log (1 + ((n : ℝ) - 1) * Real.exp (-m)) := le_trans hgap hupper
  have hexp : Real.exp g ≤ 1 + ((n : ℝ) - 1) * Real.exp (-m) := by
    have := Real.exp_le_exp.2 hglog
    rwa [Real.exp_log hpos] at this
  have hg1 : 0 < Real.exp g - 1 := by
    have := Real.add_one_le_exp g
    linarith
  have hnm1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hkey : (Real.exp g - 1) / ((n : ℝ) - 1) ≤ Real.exp (-m) := by
    rw [div_le_iff₀ hnm1]; linarith
  have hlog := Real.log_le_log (by positivity) hkey
  rw [Real.log_exp, Real.log_div (ne_of_gt hg1) (ne_of_gt hnm1)] at hlog
  linarith
