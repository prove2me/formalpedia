-- Prove2me | solution 1 for SplitCountLaw.mutualInfo_of_channel
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:50:28.591059+00:00
-- url     : https://prove2.me/submissions/8e2c3ae9-6f18-46da-97c1-1f011a189f72

-- Sol generated from Novelty/SplitCountLaw.lean
import Mathlib
import Definitions.Def_Novelty_SplitCountLaw

/-!
# Finite mutual information: log-sum, data processing, and the `I ≤ H(A)` cap

This file develops, from first principles, the small amount of information theory
needed by `Novelty.SplitCountChannel` (the SPLIT-COUNT-LAW experiment).

Everything is phrased for a *finite joint weight table* `p : α → β → ℝ` with
nonnegative entries; the mutual information is measured in **bits**:

`mutualInfo p = ∑ a ∑ b, p a b * logb 2 (p a b / (rowMarg p a * colMarg p b))`.

Main results.

* `Real.logsum_inequality` : the log-sum inequality
  `(∑ aᵢ) * log ((∑ aᵢ)/(∑ bᵢ)) ≤ ∑ aᵢ * log (aᵢ / bᵢ)` for `aᵢ ≥ 0`, `bᵢ > 0`.
* `mutualInfo_map_le` : the **data processing inequality** for a deterministic
  relabelling `g : β → γ` of the second coordinate.
* `mutualInfo_le_rowEntropy` : `I(A;B) ≤ H(A)`.
* `mutualInfo_le_one_of_binary` : for a binary first coordinate, `I(A;B) ≤ 1` bit.
* `mutualInfo_nonneg` : `I(A;B) ≥ 0`.

No probabilistic measure theory is used: all statements are elementary real
inequalities about finite tables, which is exactly the level at which the
split-count experiment lives.
-/

open SplitCountLaw

open Finset Real





/-! ## The log-sum inequality -/







/-! ## Data processing -/


variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq γ]






/-! ## The `I ≤ H(A)` cap -/


variable {α β : Type*} [Fintype α] [Fintype β]







/-! ## Channel decomposition `I = H(B) - H(B|A)` -/


variable {α β : Type*} [Fintype α] [Fintype β]



/-! ## Nonnegativity -/


variable {α β : Type*} [Fintype α] [Fintype β]






open SplitCountLaw in
theorem solution(w : α → ℝ) (k : α → β → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hk : ∀ a b, 0 ≤ k a b) (hk1 : ∀ a, ∑ b, k a b = 1)
    (hcol : ∀ b, 0 < colMarg (fun a b => w a * k a b) b) :
    mutualInfo (fun a b => w a * k a b)
      = entropyBits (colMarg (fun a b => w a * k a b)) - ∑ a, w a * entropyBits (k a) := by
  set p : α → β → ℝ := fun a b => w a * k a b with hp
  have hrow : ∀ a, rowMarg p a = w a := by
    intro a; simp only [rowMarg, hp, ← Finset.mul_sum, hk1 a, mul_one]
  have key : ∀ a b, p a b * logb 2 (p a b / (rowMarg p a * colMarg p b))
      = w a * (k a b * logb 2 (k a b)) - w a * k a b * logb 2 (colMarg p b) := by
    intro a b
    rcases eq_or_lt_of_le (hw a) with hwa | hwa
    · simp [hp, ← hwa]
    rcases eq_or_lt_of_le (hk a b) with hkab | hkab
    · simp [hp, ← hkab]
    have hdiv : p a b / (rowMarg p a * colMarg p b) = k a b / colMarg p b := by
      rw [hrow a]
      field_simp [hp]
      rfl
    rw [hdiv, Real.logb_div (ne_of_gt hkab) (ne_of_gt (hcol b))]
    simp only [hp]
    ring
  have hexp : mutualInfo p = ∑ a, ∑ b,
      (w a * (k a b * logb 2 (k a b)) - w a * k a b * logb 2 (colMarg p b)) := by
    simp only [mutualInfo]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => key a b))
  rw [hexp]
  have h1 : ∀ a : α, ∑ b, (w a * (k a b * logb 2 (k a b)) - w a * k a b * logb 2 (colMarg p b))
      = -(w a * entropyBits (k a)) - ∑ b, w a * k a b * logb 2 (colMarg p b) := by
    intro a
    rw [Finset.sum_sub_distrib]
    congr 1
    have hE : entropyBits (k a) = -∑ b, k a b * logb 2 (k a b) := by
      simp only [entropyBits, Finset.sum_neg_distrib]
    rw [hE, mul_neg, neg_neg, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_sub_distrib]
  have h2 : ∑ a, ∑ b, w a * k a b * logb 2 (colMarg p b)
      = -entropyBits (colMarg p) := by
    rw [Finset.sum_comm]
    simp only [entropyBits, ← Finset.sum_neg_distrib, neg_neg]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← Finset.sum_mul]
    rfl
  rw [h2]
  simp only [Finset.sum_neg_distrib]
  ring
