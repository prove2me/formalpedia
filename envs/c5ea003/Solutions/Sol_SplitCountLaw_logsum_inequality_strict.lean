-- Prove2me | solution 1 for SplitCountLaw.logsum_inequality_strict
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:47:50.19723+00:00
-- url     : https://prove2.me/submissions/9c8412a7-1b48-4354-9b88-fd8bbc7edd66

-- Sol generated from Novelty/SplitCountLaw.lean
import Mathlib
import Definitions.Def_Novelty_SplitCountLaw
import Theorems.Thm_SplitCountLaw_log_div_sub_log_ge
import Theorems.Thm_SplitCountLaw_log_div_sub_log_gt

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
theorem solution{ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hne : a i₀ * (∑ i ∈ s, b i) ≠ b i₀ * (∑ i ∈ s, a i)) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) <
      ∑ i ∈ s, a i * Real.log (a i / b i) := by
  set A := ∑ i ∈ s, a i with hA
  set B := ∑ i ∈ s, b i with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg ha
  have hne' : A ≠ 0 := by
    intro h
    apply hne
    have hzero : ∀ i ∈ s, a i = 0 := (Finset.sum_eq_zero_iff_of_nonneg ha).1 h
    rw [hzero i₀ hi₀, h]
    ring
  have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hne')
  have hBpos : 0 < B := by
    rcases Finset.eq_empty_or_nonempty s with rfl | hs
    · simp [hA] at hApos
    · exact Finset.sum_pos hb hs
  have hc : 0 < A / B := div_pos hApos hBpos
  have key : ∀ i ∈ s, a i - b i * (A / B) ≤ a i * Real.log (a i / b i) -
      a i * Real.log (A / B) :=
    fun i hi => log_div_sub_log_ge (ha i hi) (hb i hi) hc
  have hne₀ : a i₀ ≠ b i₀ * (A / B) := by
    intro h
    apply hne
    rw [h]
    field_simp
  have keylt : a i₀ - b i₀ * (A / B) < a i₀ * Real.log (a i₀ / b i₀) -
      a i₀ * Real.log (A / B) :=
    log_div_sub_log_gt (ha i₀ hi₀) (hb i₀ hi₀) hc hne₀
  have hsum : ∑ i ∈ s, (a i - b i * (A / B)) <
      ∑ i ∈ s, (a i * Real.log (a i / b i) - a i * Real.log (A / B)) :=
    Finset.sum_lt_sum key ⟨i₀, hi₀, keylt⟩
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul] at hsum
  rw [← hA, ← hB] at hsum
  have hBB : B * (A / B) = A := by field_simp
  rw [hBB] at hsum
  linarith
