-- Prove2me | solution 1 for Catalog.Novelty.ZeroFitDialPerturbation.rho_swap_exact
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:41:07.313498+00:00
-- url     : https://prove2.me/submissions/5b40ddd9-32ec-4120-bcfe-0817777f04cc

-- Sol generated from Novelty/ZeroFitDialPerturbation.lean
import Mathlib
import Definitions.Def_Novelty_ZeroFitDialPerturbation
import Definitions.Def_Novelty_ZeroFitDialU64
import Definitions.Def_Novelty_ZeroFitDialU76

/-!
# The corruption budget: how much re-ranking a dial move costs

Cycle 2 of the round-65 (bitlen-76) investigation.

`Novelty.ZeroFitDialU76` proves that the *tie geometry* of the zero-count statistic
is flat: between bitlen 72 and bitlen 76 the attainable Spearman ceiling moves by
less than `10^{-43}`, and between bitlen 64 and 76 by less than `10^{-30}` times the
recorded drop `0.648 → 0.608`.  So whatever moves the dial is not tie granularity —
it must act on the *ranks themselves*.

This file quantifies that alternative.  Working with raw rank vectors
`R, S : Fin n → ℚ` and the Spearman coefficient in `d²` form
`ρ = 1 - 6·Σᵢ(Rᵢ-Sᵢ)²/(n³-n)`, we prove:

* `sumSqD_sub_eq` — localisation: if `S` and `S'` agree off a set `A`, the `Σd²`
  difference is supported on `A`;
* `abs_sumSqD_sub_le` — each disagreeing coordinate can move `Σd²` by at most
  `(n-1)²`, hence `|Σd²(R,S) - Σd²(R,S')| ≤ |A|(n-1)²`;
* `abs_rho_sub_le` and `abs_rho_sub_le_div` — the **rank-perturbation Lipschitz law**
  `|ρ(R,S) - ρ(R,S')| ≤ 6|A|(n-1)/(n(n+1)) ≤ 6|A|/n`;
* `corruption_budget` — the contrapositive **budget law**: a dial move of size `δ`
  requires at least `δn/6` re-ranked observations;
* `u76_corruption_budget` — applied to the recorded `0.648 → 0.608` drop: at least
  `n/150` of the sample (0.67%) must be re-ranked;
* `sumSqD_swap_exact` and `rho_swap_exact` — sharpness: a single transposition
  changes `Σd²` by *exactly* `-2(Rᵢ-Rⱼ)(Sᵢ-Sⱼ)`, and transposing the two extreme
  ranks realises the per-coordinate bound `(n-1)²` exactly, so the Lipschitz law
  above is tight up to the constant 2.

Nothing here assumes the ranks come from any particular statistic: the bound holds
for *every* mechanism acting by re-ranking, which is what makes it a budget.
-/

open Finset

open Catalog.Novelty.ZeroFitDialPerturbation

/-- `n³ - n > 0` for a sample of size at least two. -/
lemma cube_sub_self_pos' {n : ℕ} (hn : 2 ≤ n) : (0 : ℚ) < (n : ℚ) ^ 3 - (n : ℚ) := by
  have hnq : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hfac : (n : ℚ) ^ 3 - (n : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) + 1) := by ring
  rw [hfac]
  exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)




/-! ## 1. Localisation and the per-coordinate bound -/

/-- If two response vectors agree off a set `A`, the `Σd²` difference is supported on `A`. -/
theorem sumSqD_sub_eq {n : ℕ} (R S S' : Fin n → ℚ) (A : Finset (Fin n))
    (hagree : ∀ i ∉ A, S i = S' i) :
    sumSqD R S - sumSqD R S' = ∑ i ∈ A, ((R i - S i) ^ 2 - (R i - S' i) ^ 2) := by
  have hsplit : ∑ i ∈ A, ((R i - S i) ^ 2 - (R i - S' i) ^ 2)
      = ∑ i ∈ (univ : Finset (Fin n)), ((R i - S i) ^ 2 - (R i - S' i) ^ 2) := by
    refine Finset.sum_subset (Finset.subset_univ A) ?_
    intro i _ hi
    rw [hagree i hi]
    ring
  rw [hsplit, Finset.sum_sub_distrib]
  rfl



/-! ## 2. The rank-perturbation Lipschitz law -/



/-! ## 3. The budget law -/



/-! ## 4. Sharpness: the exact transposition increment -/

/-- **Exact transposition increment.**  Swapping the response ranks of two observations
changes `Σd²` by exactly `-2(Rᵢ-Rⱼ)(Sᵢ-Sⱼ)`. -/
theorem sumSqD_swap_exact {n : ℕ} (R S S' : Fin n → ℚ) (i j : Fin n) (hij : i ≠ j)
    (hi : S' i = S j) (hj : S' j = S i) (hrest : ∀ k, k ≠ i → k ≠ j → S k = S' k) :
    sumSqD R S - sumSqD R S' = -2 * (R i - R j) * (S i - S j) := by
  have hagree : ∀ k ∉ ({i, j} : Finset (Fin n)), S k = S' k := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact hrest k hk.1 hk.2
  rw [sumSqD_sub_eq R S S' ({i, j} : Finset (Fin n)) hagree,
    Finset.sum_insert (by simpa using hij), Finset.sum_singleton, hi, hj]
  ring

/-- The transposition increment is maximal — equal to `2(n-1)²` — when the two swapped
observations carry the extreme ranks `1` and `n` on both sides.  Hence the constant in
`abs_sumSqD_sub_le` is sharp up to the factor `2` coming from `|A| = 2`. -/
theorem sumSqD_swap_extreme {n : ℕ} (R S S' : Fin n → ℚ) (i j : Fin n) (hij : i ≠ j)
    (hi : S' i = S j) (hj : S' j = S i) (hrest : ∀ k, k ≠ i → k ≠ j → S k = S' k)
    (hRi : R i = 1) (hRj : R j = (n : ℚ)) (hSi : S i = 1) (hSj : S j = (n : ℚ)) :
    sumSqD R S' - sumSqD R S = 2 * ((n : ℚ) - 1) ^ 2 := by
  have h := sumSqD_swap_exact R S S' i j hij hi hj hrest
  rw [hRi, hRj, hSi, hSj] at h
  nlinarith [h]



open Catalog.Novelty.ZeroFitDialPerturbation in
theorem solution{n : ℕ} (hn : 2 ≤ n) (R S S' : Fin n → ℚ) (i j : Fin n) (hij : i ≠ j)
    (hi : S' i = S j) (hj : S' j = S i) (hrest : ∀ k, k ≠ i → k ≠ j → S k = S' k)
    (hRi : R i = 1) (hRj : R j = (n : ℚ)) (hSi : S i = 1) (hSj : S j = (n : ℚ)) :
    rhoRank R S - rhoRank R S' = 12 * ((n : ℚ) - 1) / ((n : ℚ) * ((n : ℚ) + 1)) := by
  have hnq : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hd := sumSqD_swap_extreme R S S' i j hij hi hj hrest hRi hRj hSi hSj
  have hden : (0 : ℚ) < (n : ℚ) ^ 3 - n := cube_sub_self_pos' hn
  have hne : ((n : ℚ) ^ 3 - n) ≠ 0 := ne_of_gt hden
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have hfac : (n : ℚ) ^ 3 - n = (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) - 1) := by ring
  have hnm : (n : ℚ) - 1 ≠ 0 := ne_of_gt (by linarith)
  rw [rhoRank, rhoRank]
  have hsub : sumSqD R S' = sumSqD R S + 2 * ((n : ℚ) - 1) ^ 2 := by linarith
  rw [hsub, hfac]
  field_simp
  ring
