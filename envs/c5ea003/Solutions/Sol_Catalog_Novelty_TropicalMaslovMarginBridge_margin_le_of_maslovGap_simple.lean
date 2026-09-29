-- Prove2me | solution 1 for Catalog.Novelty.TropicalMaslovMarginBridge.margin_le_of_maslovGap_simple
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:32:05.446119+00:00
-- url     : https://prove2.me/submissions/a3053669-9719-4f34-8de8-cd330d92819b

-- Sol generated from Novelty/TropicalMaslovMarginBridge.lean
import Mathlib
import Definitions.Def_Novelty_KVDecisionDissociation
import Definitions.Def_Novelty_TropicalMaslovMarginBridge
import Theorems.Thm_Catalog_Novelty_TropicalMaslovMarginBridge_margin_le_of_maslovGap

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
    (hm : ∀ j, j ≠ i → m ≤ x i - x j) (hg : 1 ≤ g) (hgap : g ≤ maslovGap x i)
    (hn : 2 ≤ n) :
    m ≤ Real.log ((n : ℝ) - 1) + Real.log 2 - g := by
  have hg0 : 0 < g := lt_of_lt_of_le zero_lt_one hg
  have hmain := margin_le_of_maslovGap x i m g hm hg0 hgap hn
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hexp2 : (2 : ℝ) ≤ Real.exp g := by
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp g := Real.exp_le_exp.2 (by linarith)
  have hhalf : Real.exp g / 2 ≤ Real.exp g - 1 := by linarith
  have hpos : (0 : ℝ) < Real.exp g / 2 := by positivity
  have hlog := Real.log_le_log hpos hhalf
  rw [Real.log_div (ne_of_gt (Real.exp_pos g)) (by norm_num), Real.log_exp] at hlog
  linarith
