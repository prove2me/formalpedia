-- Prove2me | solution 1 for Catalog.Novelty.TropicalMaslovMarginBridge.maslovGap_le_log_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:32:06.45619+00:00
-- url     : https://prove2.me/submissions/b38bbe99-f2d0-47ba-be39-277e2ae12c65

-- Sol generated from Novelty/TropicalMaslovMarginBridge.lean
import Mathlib
import Definitions.Def_Novelty_KVDecisionDissociation
import Definitions.Def_Novelty_TropicalMaslovMarginBridge

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



theorem sum_exp_pos (x : Fin n → ℝ) (i : Fin n) : 0 < ∑ j, Real.exp (x j) :=
  Finset.sum_pos (fun j _ => Real.exp_pos (x j)) ⟨i, mem_univ i⟩




/-! ### Margin ⟹ small gap (near-tropical) -/


/-! ### Large gap ⟹ small margin (far from tropical) -/



/-! ### Small margin ⟹ flippable decision -/





open Catalog.Novelty.TropicalMaslovMarginBridge in
theorem solution(x : Fin n → ℝ) (i : Fin n) (hmax : ∀ j, x j ≤ x i) :
    maslovGap x i ≤ Real.log n := by
  have hcard : ∑ _j : Fin n, Real.exp (x i) = (n : ℝ) * Real.exp (x i) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hsum : ∑ j, Real.exp (x j) ≤ (n : ℝ) * Real.exp (x i) := by
    rw [← hcard]
    exact Finset.sum_le_sum fun j _ => Real.exp_le_exp.2 (hmax j)
  have hn : 0 < (n : ℝ) := by
    have : 0 < n := Fin.pos i
    exact_mod_cast this
  have hlog := Real.log_le_log (sum_exp_pos x i) hsum
  rw [Real.log_mul (ne_of_gt hn) (Real.exp_ne_zero _), Real.log_exp] at hlog
  simp only [maslovGap, lse]
  linarith
