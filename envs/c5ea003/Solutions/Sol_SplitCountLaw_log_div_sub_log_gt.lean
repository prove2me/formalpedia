-- Prove2me | solution 1 for SplitCountLaw.log_div_sub_log_gt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:46:18.515556+00:00
-- url     : https://prove2.me/submissions/26abff96-3ec1-4fab-aaaf-955875113ff0

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
theorem solution{x y c : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hc : 0 < c)
    (hne : x ≠ y * c) :
    x - y * c < x * Real.log (x / y) - x * Real.log c := by
  rcases eq_or_lt_of_le hx with h | hx'
  · subst_vars
    simp only [zero_mul, zero_sub, sub_zero, neg_lt_zero]
    positivity
  · have hx0 : x ≠ 0 := ne_of_gt hx'
    have hne1 : (y * c) / x ≠ 1 := by
      intro h
      apply hne
      field_simp at h
      linarith
    have hlog : Real.log ((y * c) / x) < (y * c) / x - 1 :=
      Real.log_lt_sub_one_of_pos (by positivity) hne1
    have hsplit : Real.log ((y * c) / x) = -(Real.log (x / y) - Real.log c) := by
      rw [Real.log_div (by positivity) hx0, Real.log_mul (ne_of_gt hy) (ne_of_gt hc),
        Real.log_div hx0 (ne_of_gt hy)]
      ring
    rw [hsplit] at hlog
    have hmul := (mul_lt_mul_iff_of_pos_left hx').2 hlog
    have hxx : x * ((y * c) / x - 1) = y * c - x := by field_simp
    nlinarith [hmul, hxx]
