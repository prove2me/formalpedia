-- Prove2me | solution 1 for Catalog.Novelty.TropicalMaslovMarginBridge.flip_of_small_margin
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:29:06.697301+00:00
-- url     : https://prove2.me/submissions/7901d34f-dcf6-42f4-adcc-1ea00c315f98

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







/-! ### Margin ⟹ small gap (near-tropical) -/


/-! ### Large gap ⟹ small margin (far from tropical) -/



/-! ### Small margin ⟹ flippable decision -/





open Catalog.Novelty.TropicalMaslovMarginBridge in
theorem solution(x : Fin n → ℝ) (i j : Fin n) (hij : j ≠ i) (m eta : ℝ)
    (hgap : x i - x j ≤ m) (hm : 0 ≤ m) (heta : 0 < eta) :
    ∃ y : Fin n → ℝ, (∀ k, |x k - y k| ≤ (m + eta) / 2) ∧ y i < y j ∧ ¬ IsStrictTop y i := by
  set d : ℝ := (m + eta) / 2 with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  refine ⟨Function.update (Function.update x i (x i - d)) j (x j + d), ?_, ?_, ?_⟩
  · intro k
    by_cases hkj : k = j
    · subst hkj
      rw [Function.update_self]
      have : x k - (x k + d) = -d := by ring
      rw [this, abs_neg, abs_of_pos hdpos]
    · rw [Function.update_of_ne hkj]
      by_cases hki : k = i
      · subst hki
        rw [Function.update_self]
        have : x k - (x k - d) = d := by ring
        rw [this, abs_of_pos hdpos]
      · rw [Function.update_of_ne hki]
        simpa using hdpos.le
  · rw [Function.update_of_ne (Ne.symm hij), Function.update_self, Function.update_self]
    have : x i - x j < 2 * d := by rw [hd]; linarith
    linarith
  · intro htop
    have h := htop j hij
    rw [Function.update_of_ne (Ne.symm hij), Function.update_self, Function.update_self] at h
    have h2 : x i - x j < 2 * d := by rw [hd]; linarith
    linarith
