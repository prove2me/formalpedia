-- Prove2me | solution 1 for Catalog.Novelty.ZeroFitDialPerturbation.abs_rho_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:41:06.428748+00:00
-- url     : https://prove2.me/submissions/2ddab02b-b787-4eba-82ad-01ceb5a52354

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

/-- A single coordinate can move `Σd²` by at most `(n-1)²`. -/
theorem abs_term_le {n : ℕ} (a s s' : ℚ) (ha : 1 ≤ a ∧ a ≤ (n : ℚ))
    (hs : 1 ≤ s ∧ s ≤ (n : ℚ)) (hs' : 1 ≤ s' ∧ s' ≤ (n : ℚ)) :
    |(a - s) ^ 2 - (a - s') ^ 2| ≤ ((n : ℚ) - 1) ^ 2 := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨hs1', hs2'⟩ := hs'
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (a - s), sq_nonneg (a - s'), sq_nonneg (s - s')]

/-- **Localised stability of `Σd²`.**  Changing the response ranking on a set `A`
moves `Σd²` by at most `|A|·(n-1)²`. -/
theorem abs_sumSqD_sub_le {n : ℕ} (R S S' : Fin n → ℚ) (hR : IsRankVec n R)
    (hS : IsRankVec n S) (hS' : IsRankVec n S') (A : Finset (Fin n))
    (hagree : ∀ i ∉ A, S i = S' i) :
    |sumSqD R S - sumSqD R S'| ≤ (A.card : ℚ) * ((n : ℚ) - 1) ^ 2 := by
  rw [sumSqD_sub_eq R S S' A hagree]
  calc |∑ i ∈ A, ((R i - S i) ^ 2 - (R i - S' i) ^ 2)|
      ≤ ∑ i ∈ A, |(R i - S i) ^ 2 - (R i - S' i) ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ A, ((n : ℚ) - 1) ^ 2 := by
        refine Finset.sum_le_sum ?_
        intro i _
        exact abs_term_le (R i) (S i) (S' i) (hR i) (hS i) (hS' i)
    _ = (A.card : ℚ) * ((n : ℚ) - 1) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## 2. The rank-perturbation Lipschitz law -/



/-! ## 3. The budget law -/



/-! ## 4. Sharpness: the exact transposition increment -/





open Catalog.Novelty.ZeroFitDialPerturbation in
theorem solution{n : ℕ} (hn : 2 ≤ n) (R S S' : Fin n → ℚ) (hR : IsRankVec n R)
    (hS : IsRankVec n S) (hS' : IsRankVec n S') (A : Finset (Fin n))
    (hagree : ∀ i ∉ A, S i = S' i) :
    |rhoRank R S - rhoRank R S'|
      ≤ 6 * (A.card : ℚ) * ((n : ℚ) - 1) ^ 2 / ((n : ℚ) ^ 3 - n) := by
  have hnq : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hden : (0 : ℚ) < (n : ℚ) ^ 3 - n := cube_sub_self_pos' hn
  have hdiff : rhoRank R S - rhoRank R S'
      = 6 * (sumSqD R S' - sumSqD R S) / ((n : ℚ) ^ 3 - n) := by
    rw [rhoRank, rhoRank]
    field_simp
    ring
  rw [hdiff, abs_div, abs_of_pos hden, div_le_div_iff_of_pos_right hden]
  have hbase := abs_sumSqD_sub_le R S S' hR hS hS' A hagree
  have hsym : |sumSqD R S' - sumSqD R S| = |sumSqD R S - sumSqD R S'| := abs_sub_comm _ _
  calc |6 * (sumSqD R S' - sumSqD R S)| = 6 * |sumSqD R S' - sumSqD R S| := by
        rw [abs_mul]; norm_num
    _ = 6 * |sumSqD R S - sumSqD R S'| := by rw [hsym]
    _ ≤ 6 * ((A.card : ℚ) * ((n : ℚ) - 1) ^ 2) := by linarith
    _ = 6 * (A.card : ℚ) * ((n : ℚ) - 1) ^ 2 := by ring
