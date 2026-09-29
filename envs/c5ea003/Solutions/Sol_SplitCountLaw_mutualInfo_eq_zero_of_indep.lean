-- Prove2me | solution 1 for SplitCountLaw.mutualInfo_eq_zero_of_indep
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:47:50.6531+00:00
-- url     : https://prove2.me/submissions/cdae9d0c-c45d-4d63-b3dc-21329a02e870

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
theorem solution(w : α → ℝ) (v : β → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hv : ∀ b, 0 ≤ v b)
    (hw1 : ∑ a, w a = 1) (hv1 : ∑ b, v b = 1) :
    mutualInfo (fun a b => w a * v b) = 0 := by
  have hrow : ∀ a, rowMarg (fun a b => w a * v b) a = w a := by
    intro a; simp only [rowMarg, ← Finset.mul_sum, hv1, mul_one]
  have hcol : ∀ b, colMarg (fun a b => w a * v b) b = v b := by
    intro b
    simp only [colMarg]
    rw [← Finset.sum_mul, hw1, one_mul]
  simp only [mutualInfo, hrow, hcol]
  refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
  rcases eq_or_lt_of_le (hw a) with h | ha
  · simp [← h]
  rcases eq_or_lt_of_le (hv b) with h | hb
  · simp [← h]
  rw [div_self (by positivity)]
  simp
