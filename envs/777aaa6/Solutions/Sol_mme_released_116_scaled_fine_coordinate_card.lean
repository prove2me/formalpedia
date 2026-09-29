-- Prove2me | solution 1 for mme_released_116_scaled_fine_coordinate_card
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T14:07:12.485352+00:00
-- url     : https://prove2.me/submissions/f747a7d6-1310-4712-85c6-7e6f6487c7a7

import Theorems.Thm_mme_released_116_regional_total
import Definitions.Def_mme_released_116_integer_profiles
import Mathlib.Data.Fintype.Sigma
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_mme_recursive_yz_CW_cells
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity

set_option autoImplicit false

/-- The repair budget has logarithmic cost controlled by the capacity,
with the base-change factor exposed for choosing the repair scale. -/
private theorem mme_repair_budget_log_le (d C : ℕ) :
    Real.log ((8 : ℝ) ^ (Nat.log d C + 1)) ≤
      Real.log 8 + (Real.log 8 / Real.log d) * Real.log C := by
  have h := Real.natLog_le_logb C d
  have h8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hm := mul_le_mul_of_nonneg_right h h8
  rw [Real.log_pow]
  simp only [Real.logb, Nat.cast_add, Nat.cast_one] at hm ⊢
  convert add_le_add_right hm (Real.log 8) using 1 <;> ring

/-- One repair scale makes its logarithmic cost an arbitrarily small
fraction of log capacity, uniformly over every natural capacity. -/
private theorem mme_repair_scale_exists_uniform_log_loss (delta : ℝ) (hdelta : 0 < delta) :
    ∃ d : ℕ, 1 < d ∧ ∀ C : ℕ,
      Real.log ((8 : ℝ) ^ (Nat.log d C + 1)) ≤ Real.log 8 + delta * Real.log C := by
  obtain ⟨s, hs⟩ := exists_nat_gt (1 / delta)
  let d := 8 ^ (s + 1)
  have hd : 1 < d := by
    dsimp [d]
    rw [pow_succ]
    have hp : 0 < 8 ^ s := pow_pos (by decide) _
    omega
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hdR : (1 : ℝ) < d := by exact_mod_cast hd
  have hlogd : Real.log (d : ℝ) = ((s : ℝ) + 1) * Real.log 8 := by
    simp [d, Nat.cast_pow, Real.log_pow]
  have hs' : 1 < (s : ℝ) * delta := (div_lt_iff₀ hdelta).mp hs
  have hratio : Real.log 8 / Real.log d ≤ delta := by
    apply (div_le_iff₀ (Real.log_pos hdR)).mpr
    rw [hlogd]
    nlinarith
  refine ⟨d, hd, fun C => (mme_repair_budget_log_le d C).trans ?_⟩
  exact add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_right hratio (Real.log_natCast_nonneg C))


open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
open scoped Classical
set_option autoImplicit false

/-- Every graded profile is a subset of the complete-word functions on its
positions, so three mode profiles have at most the unrestricted triple count. -/
private theorem mme_profile_capacity_le_unrestricted
    {P C : Type*} [Fintype P] (ell : ℕ) (cell : P → C)
    (shape : C → Fin 3 → ℕ) (mu : Fin 3 → C → CompleteWord ell → ℕ) :
    (∏ i : Fin 3, Nat.card (Block ell cell shape mu i)) ≤
      3 ^ (3 * (Fintype.card P * 2 ^ (ell - 1))) := by
  have h (i : Fin 3) : Nat.card (Block ell cell shape mu i) ≤
      (3 ^ (2 ^ (ell - 1))) ^ Fintype.card P := by
    have h := Nat.card_le_card_of_injective
      (fun f : Block ell cell shape mu i => f.val) Subtype.val_injective
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] using h
  calc
    _ ≤ ∏ _ : Fin 3, (3 ^ (2 ^ (ell - 1))) ^ Fintype.card P :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => h i)
    _ = _ := by simp [← pow_mul, Nat.mul_comm]

/-- The logarithm of the repair capacity is bounded linearly in the number
of fine-word coordinates, independently of the specific profiles. -/
private theorem mme_profile_capacity_log_le_fine_length
    {P C : Type*} [Fintype P] (ell : ℕ) (cell : P → C)
    (shape : C → Fin 3 → ℕ) (mu : Fin 3 → C → CompleteWord ell → ℕ) :
    Real.log (∏ i : Fin 3, Nat.card (Block ell cell shape mu i) : ℕ) ≤
      (3 * (Fintype.card P * 2 ^ (ell - 1)) : ℕ) * Real.log 3 := by
  let cap := ∏ i : Fin 3, Nat.card (Block ell cell shape mu i)
  by_cases hc : cap = 0
  · change Real.log (cap : ℝ) ≤ _
    rw [hc, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  · have hpos : (0 : ℝ) < cap := by exact_mod_cast Nat.pos_of_ne_zero hc
    have hbound : (cap : ℝ) ≤ (3 : ℝ) ^ (3 * (Fintype.card P * 2 ^ (ell - 1))) := by
      exact_mod_cast mme_profile_capacity_le_unrestricted ell cell shape mu
    have h := Real.log_le_log hpos hbound
    rw [Real.log_pow] at h
    exact h


/-- One repair scale makes the logarithmic repair budget at most eta per
fine coordinate, up to the fixed log-eight overhead, for every profile. -/
private theorem mme_profile_repair_scale_exists_uniform_coordinate_loss
    (eta : ℝ) (heta : 0 < eta) :
    ∃ d : ℕ, 1 < d ∧ ∀ (ell : ℕ) (P C : Type*) [Fintype P]
      (cell : P → C) (shape : C → Fin 3 → ℕ)
      (mu : Fin 3 → C → CompleteWord ell → ℕ),
      Real.log ((8 : ℝ) ^ (Nat.log d
        (∏ i : Fin 3, Nat.card (Block ell cell shape mu i)) + 1)) ≤
        Real.log 8 + eta * (Fintype.card P * 2 ^ (ell - 1) : ℕ) := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hden : 0 < 3 * Real.log 3 := mul_pos (by norm_num) h3
  obtain ⟨d, hd, hbudget⟩ := mme_repair_scale_exists_uniform_log_loss
    (eta / (3 * Real.log 3)) (div_pos heta hden)
  refine ⟨d, hd, ?_⟩
  intro ell P C inst cell shape mu
  have hcap := mme_profile_capacity_log_le_fine_length ell cell shape mu
  calc
    _ ≤ Real.log 8 + (eta / (3 * Real.log 3)) *
        Real.log (∏ i : Fin 3, Nat.card (Block ell cell shape mu i) : ℕ) := hbudget _
    _ ≤ Real.log 8 + (eta / (3 * Real.log 3)) *
        ((3 * (Fintype.card P * 2 ^ (ell - 1)) : ℕ) * Real.log 3) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hcap (div_pos heta hden).le)
    _ = _ := by
      push_cast
      field_simp


open MME.Released116 MME.MoreAsymmetryExactSeed

/-- The released six-region child positions occupy exactly four fine
coordinates per replicated parent position. -/
theorem solution (k : ℕ) :
    Fintype.card (Position (fun r : Fin 6 => k * regionalSize r)) * 2 ^ (2 - 1) =
      4 * (k * denominator ^ 4) := by
  simp only [Position, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  rw [← Finset.sum_mul, ← Finset.mul_sum, mme_released_116_regional_total]
  ring

/-- One repair scale controls every replicated released profile, uniformly
in the reference address, at eta per physical fine coordinate. -/
private theorem mme_released_116_uniform_repair_coordinate_loss (eta : ℝ) (heta : 0 < eta) :
    ∃ d : ℕ, 1 < d ∧ ∀ (k : ℕ)
      (reference : MME.RecursiveXHash.Address 4 6 parent
        (fun r => k * regionalSize r)),
      Real.log ((8 : ℝ) ^ (Nat.log d
        (∏ i : Fin 3, Nat.card (Block 2 (fullCell parent_total reference)
          (fun c i => (c.2.val i).val) (fun i c w => k * integerProfile i c w) i)) + 1)) ≤
        Real.log 8 + eta * (4 * (k * denominator ^ 4) : ℕ) := by
  obtain ⟨d, hd, hbudget⟩ := mme_profile_repair_scale_exists_uniform_coordinate_loss eta heta
  refine ⟨d, hd, ?_⟩
  intro k reference
  have h := hbudget 2 _ _ (fullCell parent_total reference)
    (fun c i => (c.2.val i).val) (fun i c w => k * integerProfile i c w)
  rw [solution] at h
  exact h


#print axioms solution
