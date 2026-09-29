-- Prove2me | solution 1 for SplitCountLaw.mutualInfo_le_rowEntropy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:50:09.220128+00:00
-- url     : https://prove2.me/submissions/8aee5a19-6af6-4f68-a4cc-94bc42bb40bb

-- Sol generated from Novelty/SplitCountLaw.lean
import Mathlib
import Definitions.Def_Novelty_SplitCountLaw
import Theorems.Thm_SplitCountLaw_mutualInfo_split

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
    mutualInfo p ≤ entropyBits (rowMarg p) := by
  have hle : ∑ a, ∑ b, p a b * logb 2 (p a b / colMarg p b) ≤ 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_nonpos (fun b _ => Finset.sum_nonpos (fun a _ => ?_))
    rcases eq_or_lt_of_le (hp a b) with h | h
    · simp [← h]
    · have hb : p a b ≤ colMarg p b :=
        Finset.single_le_sum (f := fun a' => p a' b) (fun a' _ => hp a' b) (Finset.mem_univ a)
      have hle1 : p a b / colMarg p b ≤ 1 := by rw [div_le_one (hcol b)]; exact hb
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h)
        (Real.logb_nonpos (by norm_num) (le_of_lt (div_pos h (hcol b))) hle1)
  have := mutualInfo_split p hp hrow hcol
  linarith
