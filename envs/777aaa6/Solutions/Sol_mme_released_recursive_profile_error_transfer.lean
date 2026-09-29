-- Prove2me | solution 1 for mme_released_recursive_profile_error_transfer
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T17:11:59.882571+00:00
-- url     : https://prove2.me/submissions/e62914e4-fc86-4568-a070-d0c5edc21a34

import Theorems.Thm_mme_released_recursive_profile_identity
open BigOperators MME MME.ReleasedGlobal MME.ReleasedMixture
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem primitive_bounds : ∀ (o : Fin 6) (s : Fin 45),
    alpha o s ≤ D ∧
      ((term o s).boundary = [] → ∑ r : Fin 6, regionWeight (term o s) r = D) := by
  decide +kernel

attribute [local irreducible] alpha term regionWeight regionProfile parentProfile profile shapeEquiv

private theorem weighted_error {R : Type*} [Fintype R] (p f g : R → ℝ) (A eps : ℝ)
    (hp : ∀ r, 0 ≤ p r) (hsum : ∑ r, p r = 1)
    (hA : 0 ≤ A) (hA1 : A ≤ 1) (heps : 0 ≤ eps)
    (hclose : ∀ r, |f r - g r| ≤ eps) :
    |A * (∑ r, p r * f r) - A * (∑ r, p r * g r)| ≤ eps := by
  calc
    _ = A * |∑ r, p r * (f r - g r)| := by
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      simp only [← mul_sub]
      rw [abs_mul, abs_of_nonneg hA]
    _ ≤ A * ∑ r, |p r * (f r - g r)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hA
    _ = A * ∑ r, p r * |f r - g r| := by
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      rw [abs_mul, abs_of_nonneg (hp r)]
    _ ≤ A * ∑ r, p r * eps := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact Finset.sum_le_sum (fun r _ ↦ mul_le_mul_of_nonneg_left (hclose r) (hp r))
    _ = A * eps := by rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ eps := by nlinarith

/-- An error bound on the six recursive regions passes to the literal global
frequency without amplification, including the global parent mass. -/
theorem solution (o : Fin 6) (i : Fin 3) (c : Shape) (w : Word)
    (f : Fin 6 → ℝ) (eps : ℝ) (heps : 0 ≤ eps)
    (hinterior : (term o (shapeEquiv.symm c)).boundary = [])
    (hclose : ∀ r, |f r - regionProfile (term o (shapeEquiv.symm c)) r (roles o i) w| ≤ eps) :
    |((alpha o (shapeEquiv.symm c) : ℝ) / D) *
      (∑ r : Fin 6, ((regionWeight (term o (shapeEquiv.symm c)) r : ℝ) / D) * f r) -
        (profile o).2 i ⟨0,c⟩ w| ≤ eps := by
  have hd : (0 : ℝ) < D := by norm_num [D, MoreAsymmetryExactSeed.denominator]
  have hb := primitive_bounds o (shapeEquiv.symm c)
  have hsum : (∑ r : Fin 6, (regionWeight (term o (shapeEquiv.symm c)) r : ℝ) / D) = 1 := by
    rw [← Finset.sum_div, ← Nat.cast_sum, hb.2 hinterior]
    exact div_self (ne_of_gt hd)
  have hA : (alpha o (shapeEquiv.symm c) : ℝ) / D ≤ 1 := by
    apply (div_le_one hd).mpr
    exact_mod_cast hb.1
  rw [(mme_released_recursive_profile_identity o i c w).2]
  unfold parentProfile
  rw [if_pos hinterior]
  exact weighted_error _ _ _ _ _ (fun _ ↦ div_nonneg (Nat.cast_nonneg _) (le_of_lt hd))
    hsum (div_nonneg (Nat.cast_nonneg _) (le_of_lt hd)) hA heps hclose
