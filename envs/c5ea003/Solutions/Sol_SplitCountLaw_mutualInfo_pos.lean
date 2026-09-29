-- Prove2me | solution 1 for SplitCountLaw.mutualInfo_pos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:50:29.163536+00:00
-- url     : https://prove2.me/submissions/fb38b816-cdc0-43f0-a797-aea042ce9725

-- Sol generated from Novelty/SplitCountLaw.lean
import Mathlib
import Definitions.Def_Novelty_SplitCountLaw
import Theorems.Thm_SplitCountLaw_logsum_inequality_strict

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






/-- `logb 2` version of the strict log-sum inequality. -/
theorem logsum_inequality_strict_logb {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hne : a i₀ * (∑ i ∈ s, b i) ≠ b i₀ * (∑ i ∈ s, a i)) :
    (∑ i ∈ s, a i) * logb 2 ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) <
      ∑ i ∈ s, a i * logb 2 (a i / b i) := by
  have h := logsum_inequality_strict s a b ha hb hi₀ hne
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) / Real.log 2 <
      (∑ i ∈ s, a i * Real.log (a i / b i)) / Real.log 2 := by
    exact div_lt_div_of_pos_right h hl2
  simpa [Real.logb, Finset.sum_div, mul_div_assoc] using hdiv

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
    (hrow : ∀ a, 0 < rowMarg p a) (hcol : ∀ b, 0 < colMarg p b)
    (htot : ∑ a, rowMarg p a = 1) {a₀ : α} {b₀ : β}
    (hne : p a₀ b₀ ≠ rowMarg p a₀ * colMarg p b₀) :
    0 < mutualInfo p := by
  have hcolsum : ∑ b, colMarg p b = 1 := by
    simpa [rowMarg, colMarg, Finset.sum_comm (f := fun a b => p a b)] using htot
  have hA : ∑ x : α × β, p x.1 x.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simpa [rowMarg] using htot
  have hB : ∑ x : α × β, rowMarg p x.1 * colMarg p x.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hcolsum, mul_one]
    simpa using htot
  have hne' : p (a₀, b₀).1 (a₀, b₀).2 * (∑ x : α × β, rowMarg p x.1 * colMarg p x.2)
      ≠ (rowMarg p (a₀, b₀).1 * colMarg p (a₀, b₀).2) * (∑ x : α × β, p x.1 x.2) := by
    rw [hA, hB]
    simpa using hne
  have h := logsum_inequality_strict_logb (Finset.univ : Finset (α × β))
    (fun x => p x.1 x.2) (fun x => rowMarg p x.1 * colMarg p x.2)
    (fun x _ => hp x.1 x.2) (fun x _ => mul_pos (hrow x.1) (hcol x.2))
    (Finset.mem_univ (a₀, b₀)) hne'
  rw [hA, hB] at h
  simp only [div_one, Real.logb_one, mul_zero] at h
  have hI : mutualInfo p = ∑ x : α × β, p x.1 x.2 *
      logb 2 (p x.1 x.2 / (rowMarg p x.1 * colMarg p x.2)) := by
    rw [Fintype.sum_prod_type]; rfl
  rw [hI]
  linarith
