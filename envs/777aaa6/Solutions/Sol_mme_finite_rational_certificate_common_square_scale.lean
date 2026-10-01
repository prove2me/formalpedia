-- Prove2me | solution 1 for mme_finite_rational_certificate_common_square_scale
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-30T21:12:51.711267+00:00
-- url     : https://prove2.me/submissions/8a68758c-94fd-46b2-9f0f-6281eed5eacb

import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
set_option autoImplicit false

/-- Clear a finite family of nonnegative rational denominators simultaneously. -/
private theorem common_natural_scale {I : Type*} [Fintype I]
    (q : I → ℚ) (hq : ∀ i, 0 ≤ q i) :
    ∃ D : ℕ, 0 < D ∧ ∃ a : I → ℕ, ∀ i, (a i : ℚ) = D * q i := by
  classical
  let D : ℕ := ∏ i, (q i).den
  have hD : 0 < D := Finset.prod_pos (fun i _ ↦ (q i).den_pos)
  have hd (i : I) : (q i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  refine ⟨D, hD, fun i ↦ (D / (q i).den) * (q i).num.toNat, ?_⟩
  intro i
  have hnum : ((q i).num.toNat : ℚ) = ((q i).num : ℚ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hq i))]
  have hmul : (D / (q i).den : ℕ) * (q i).den = D := Nat.div_mul_cancel (hd i)
  have hmulQ : ((D / (q i).den : ℕ) : ℚ) * ((q i).den : ℚ) = (D : ℚ) := by
    exact_mod_cast hmul
  have hden : ((q i).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (q i).den_ne_zero
  have hnumQ : ((q i).num : ℚ) = q i * ((q i).den : ℚ) :=
    (div_eq_iff hden).mp (Rat.num_div_den (q i))
  calc
    _ = ((D / (q i).den : ℕ) : ℚ) * ((q i).num : ℚ) := by rw [Nat.cast_mul, hnum]
    _ = (((D / (q i).den : ℕ) : ℚ) * ((q i).den : ℚ)) * q i := by rw [hnumQ]; ring
    _ = _ := by rw [hmulQ]

/-- One scale simultaneously clears every finite nonnegative rational table,
including joint tables, and preserves arbitrary rational linear constraints. -/
theorem solution
    {I : Type*} [Fintype I] (q : I → ℚ) (hq : ∀ i, 0 ≤ q i) :
    ∃ D : ℕ, 0 < D ∧ ∃ a : I → ℕ,
      (∀ i, (a i : ℚ) = (D : ℚ) * q i) ∧
      (∀ k : ℕ, ∀ i, ((k ^ 2 * a i : ℕ) : ℚ) = ((k ^ 2 * D : ℕ) : ℚ) * q i) ∧
      (∀ k : ℕ, ∀ coeff : I → ℚ, ∀ target : ℚ,
        (∑ i, coeff i * q i) = target →
        (∑ i, coeff i * ((k ^ 2 * a i : ℕ) : ℚ)) =
          ((k ^ 2 * D : ℕ) : ℚ) * target) ∧
      (∀ k : ℕ, 0 < k → ∀ i, 0 < q i → 0 < k ^ 2 * a i) := by
  classical
  obtain ⟨D, hD, a, ha⟩ := common_natural_scale q hq
  have hs (k : ℕ) (i : I) : ((k ^ 2 * a i : ℕ) : ℚ) =
      ((k ^ 2 * D : ℕ) : ℚ) * q i := by
    push_cast
    rw [ha i]
    ring
  refine ⟨D, hD, a, ha, hs, ?_, ?_⟩
  · intro k coeff target ht
    rw [← ht, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hs k i]
    ring
  · intro k hk i hi
    have hp : 0 < (a i : ℚ) := by rw [ha i]; exact mul_pos (Nat.cast_pos.mpr hD) hi
    exact Nat.mul_pos (pow_pos hk _) (Nat.cast_pos.mp hp)

#print axioms solution
