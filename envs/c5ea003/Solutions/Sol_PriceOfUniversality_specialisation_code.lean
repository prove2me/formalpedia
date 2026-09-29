-- Prove2me | solution 1 for PriceOfUniversality.specialisation_code
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:24:22.386757+00:00
-- url     : https://prove2.me/submissions/1f6da89a-57b5-4df7-924c-059b1f45dc78

-- Sol generated from Novelty/UniversalRedundancySharpness.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyProduct
import Definitions.Def_Novelty_UniversalRedundancySharpness
import Theorems.Thm_PriceOfUniversality_redundancy_indicatorClass
/-
# The price of universality, VI: sharpness, non-vacuity and the two-sided rate

Adversarial review of the preceding files.  Two questions are settled here.

**1. Are the hypotheses of the "exact price" theorems satisfiable?**
`indicatorClass_sandwich` exhibits a concrete class — the `m` deterministic
sources on an alphabet of size `m` — that satisfies every hypothesis of
`price_of_universality_sandwich` and `minimax_regret_disjoint`, so those results
are not vacuous.  For this class the general theory specialises to a sharp
pigeonhole statement about code lengths, `exists_length_ge_logb_card`: any Kraft
code on `m` messages assigns some message a length of at least `log₂ m`.

**2. Is the `(1/2) log₂ n` lower bound of the Bernoulli class of the right
order?**  `shtarkov_bernClass_le` shows `S ≤ n + 1`, hence the exact minimax
regret of the memoryless binary class of block length `n` obeys

  `(1/2) log₂ n − 2  ≤  regret  ≤  log₂ (n + 1)`.

So the truth is pinned between `(1/2) log₂ n` and `log₂ n`; the classical
`(1/2) log₂ n + O(1)` answer sits at the lower end, and no bound better than
linear in `log n` is possible.  Closing the factor-of-two gap requires the
Stirling-type estimate discussed in `FUTURE_DIRECTIONS.md`.
-/

open PriceOfUniversality

open Finset Real

/-! ## Bridge: the average-case price never exceeds the worst-case price -/


variable {A : Type*} [Fintype A] [Nonempty A] {Θ : Type*} [Fintype Θ] [Nonempty Θ]




/-! ## A concrete class realising the exact price `log₂ m` -/


variable {m : ℕ}









/-! ## The Bernoulli class: matching upper bound of order `log n` -/






open PriceOfUniversality in
theorem solution[NeZero m] (θ : Fin m) :
    ∃ L : Fin m → ℕ, IsCode L ∧ redundancy (indicatorClass m θ) L ≤ 1 := by
  classical
  refine ⟨fun a => if a = θ then 1 else m + 1, ?_, ?_⟩
  · have hsum : kraftSum (fun a : Fin m => if a = θ then 1 else m + 1)
        = ((2:ℝ)⁻¹) ^ 1 + ∑ _a ∈ univ.erase θ, ((2:ℝ)⁻¹) ^ (m + 1) := by
      rw [kraftSum, ← Finset.add_sum_erase _ _ (mem_univ θ)]
      congr 1
      · simp
      · exact Finset.sum_congr rfl fun a ha => by
          rw [if_neg (Finset.ne_of_mem_erase ha)]
    have hcard : (univ.erase θ).card = m - 1 := by
      rw [Finset.card_erase_of_mem (mem_univ θ), Finset.card_univ, Fintype.card_fin]
    have hconst : ∑ _a ∈ univ.erase θ, ((2:ℝ)⁻¹) ^ (m + 1)
        = ((m - 1 : ℕ) : ℝ) * ((2:ℝ)⁻¹) ^ (m + 1) := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul]
    have hmle : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
      have : (m - 1 : ℕ) ≤ m := Nat.sub_le _ _
      exact_mod_cast this
    have hpow : (m : ℝ) ≤ (2:ℝ) ^ m := by
      have : m < 2 ^ m := Nat.lt_two_pow_self
      exact_mod_cast this.le
    have h2m : (0:ℝ) < (2:ℝ) ^ m := by positivity
    have hkey : ((m - 1 : ℕ) : ℝ) * ((2:ℝ)⁻¹) ^ (m + 1) ≤ (2:ℝ)⁻¹ := by
      have hinv : ((2:ℝ)⁻¹) ^ (m + 1) = ((2:ℝ) ^ (m + 1))⁻¹ := by
        rw [inv_pow]
      rw [hinv, pow_succ]
      rw [mul_inv_le_iff₀ (by positivity)]
      have : (2:ℝ)⁻¹ * ((2:ℝ) ^ m * 2) = (2:ℝ) ^ m := by
        field_simp
      rw [this]
      linarith
    rw [IsCode, hsum, hconst]
    have : ((2:ℝ)⁻¹) ^ 1 = (2:ℝ)⁻¹ := pow_one _
    rw [this]
    linarith
  · rw [redundancy_indicatorClass]
    simp
