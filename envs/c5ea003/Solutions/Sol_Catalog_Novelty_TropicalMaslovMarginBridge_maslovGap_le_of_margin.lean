-- Prove2me | solution 1 for Catalog.Novelty.TropicalMaslovMarginBridge.maslovGap_le_of_margin
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:29:07.6505+00:00
-- url     : https://prove2.me/submissions/d290d86a-3d92-44eb-bcef-7ca087e9594e

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
theorem solution(x : Fin n → ℝ) (i : Fin n) (m : ℝ)
    (hm : ∀ j, j ≠ i → m ≤ x i - x j) :
    maslovGap x i ≤ Real.log (1 + ((n : ℝ) - 1) * Real.exp (-m)) := by
  have hn1 : 1 ≤ n := Fin.pos i
  have hcard : ((univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (mem_univ i)]
    simp [Nat.cast_sub hn1]
  have hterm : ∀ j ∈ univ.erase i, Real.exp (x j) ≤ Real.exp (x i) * Real.exp (-m) := by
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.1 hj).1
    have : x j ≤ x i + -m := by linarith [hm j hji]
    calc Real.exp (x j) ≤ Real.exp (x i + -m) := Real.exp_le_exp.2 this
      _ = Real.exp (x i) * Real.exp (-m) := Real.exp_add _ _
  have hsplit : ∑ j, Real.exp (x j)
      = Real.exp (x i) + ∑ j ∈ univ.erase i, Real.exp (x j) :=
    (Finset.add_sum_erase univ (fun j => Real.exp (x j)) (mem_univ i)).symm
  have htail : ∑ j ∈ univ.erase i, Real.exp (x j)
      ≤ ((n : ℝ) - 1) * (Real.exp (x i) * Real.exp (-m)) := by
    calc ∑ j ∈ univ.erase i, Real.exp (x j)
        ≤ ∑ _j ∈ univ.erase i, Real.exp (x i) * Real.exp (-m) :=
          Finset.sum_le_sum hterm
      _ = ((univ.erase i).card : ℝ) * (Real.exp (x i) * Real.exp (-m)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ = ((n : ℝ) - 1) * (Real.exp (x i) * Real.exp (-m)) := by rw [hcard]
  have hbound : ∑ j, Real.exp (x j)
      ≤ Real.exp (x i) * (1 + ((n : ℝ) - 1) * Real.exp (-m)) := by
    rw [hsplit]; nlinarith [htail]
  have hpos : (0 : ℝ) < 1 + ((n : ℝ) - 1) * Real.exp (-m) := by
    have h1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      linarith
    have := Real.exp_pos (-m)
    nlinarith
  have hlog := Real.log_le_log (sum_exp_pos x i) hbound
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hpos), Real.log_exp] at hlog
  simp only [maslovGap, lse]
  linarith
