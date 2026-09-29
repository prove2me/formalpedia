-- Prove2me | solution 1 for SplitCountLaw.mutualInfo_split
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:47:51.151983+00:00
-- url     : https://prove2.me/submissions/efd69982-96a9-4183-b7c5-c4223a07593e

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
theorem solution(p : α → β → ℝ) (hp : ∀ a b, 0 ≤ p a b)
    (hrow : ∀ a, 0 < rowMarg p a) (hcol : ∀ b, 0 < colMarg p b) :
    mutualInfo p = (∑ a, ∑ b, p a b * logb 2 (p a b / colMarg p b))
      + entropyBits (rowMarg p) := by
  have hsplit : ∀ a b, p a b * logb 2 (p a b / (rowMarg p a * colMarg p b))
      = p a b * logb 2 (p a b / colMarg p b) - p a b * logb 2 (rowMarg p a) := by
    intro a b
    rcases eq_or_lt_of_le (hp a b) with h | h
    · simp [← h]
    · have h1 : p a b / (rowMarg p a * colMarg p b)
          = (p a b / colMarg p b) / rowMarg p a := by
        field_simp
      rw [h1, Real.logb_div (div_ne_zero (ne_of_gt h) (ne_of_gt (hcol b))) (ne_of_gt (hrow a))]
      ring
  simp only [mutualInfo, entropyBits]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_congr rfl (fun b _ => hsplit a b), Finset.sum_sub_distrib, ← Finset.sum_mul]
  have : (∑ b, p a b) = rowMarg p a := rfl
  rw [this]
  ring
