-- Prove2me | solution 1 for mme_regional_parent_windows_imply_global_histogram_window_allow_empty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T04:03:36.746223+00:00
-- url     : https://prove2.me/submissions/6dc9a60a-fe13-41b4-8c79-c66d7c0f4af4

import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open scoped Classical
set_option autoImplicit false

/-- A partition of physical parent positions splits a full-word histogram
into the exact pair-word histograms of its regions. -/
private theorem mme_parent_histogram_sum_over_regions
    {P A W : Type} [Fintype P] {R : ℕ} {n : Fin R → ℕ}
    (positions : (Σ r, Fin (n r)) ≃ P) (f : P → A)
    (pair : A ≃ (Fin 2 → W)) (a : A) :
    Fintype.card {p : P // f p = a} =
      ∑ r, Fintype.card {t : Fin (n r) //
        ∀ h, pair (f (positions ⟨r,t⟩)) h = pair a h} := by
  classical
  have hinj : Function.Injective (fun p : (Σ r, {t : Fin (n r) //
      ∀ h, pair (f (positions ⟨r,t⟩)) h = pair a h}) =>
      (⟨p.1,p.2.val⟩ : Σ r, Fin (n r))) := by
    rintro ⟨r,t,ht⟩ ⟨s,u,hu⟩ heq
    cases heq
    rfl
  let e : (Σ r, {t : Fin (n r) //
      ∀ h, pair (f (positions ⟨r,t⟩)) h = pair a h}) ≃
      {p : P // f p = a} := {
    toFun := fun p => ⟨positions ⟨p.1,p.2.val⟩, pair.injective (funext p.2.property)⟩
    invFun := fun p => ⟨(positions.symm p.val).1,
      ⟨(positions.symm p.val).2, by
        intro h
        simp only [Sigma.eta, Equiv.apply_symm_apply, p.property]⟩⟩
    left_inv := by
      intro p
      apply hinj
      exact positions.symm_apply_apply ⟨p.1,p.2.val⟩
    right_inv := by intro p; apply Subtype.ext; exact positions.apply_symm_apply p.val }
  rw [← Fintype.card_congr e, Fintype.card_sigma]

/-- Regional parent windows imply the full-word histogram window around
the regional-size-weighted mean of their centers, allowing empty regions. -/
theorem solution
    {P A W : Type} [Fintype P] [Fintype W]
    {half R T : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ)
    (positions : (Σ r, Fin (n r)) ≃ P) (f : P → A)
    (pair : A ≃ (Fin 2 → W)) (eps : ℝ)
    (hT : ∑ r, n r = T) (hTpos : 0 < T)
    (htypical : parentTypical htotal n m mu eps
      (fun p => pair (f (positions ⟨p.1,p.2.1⟩)) p.2.2)) :
    ∀ a : A, |(Fintype.card {p : P // f p = a} : ℝ) / T -
      ∑ r, ((n r : ℝ) / T) * parentMixture htotal n m mu r (pair a)| ≤ eps := by
  classical
  intro a
  let H (r : Fin R) := Fintype.card {t : Fin (n r) //
    ∀ h, pair (f (positions ⟨r,t⟩)) h = pair a h}
  have hcount := mme_parent_histogram_sum_over_regions positions f pair a
  have hTr : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hnr (r : Fin R) : (0 : ℝ) ≤ n r := Nat.cast_nonneg _
  have hlocal (r : Fin R) :
      |(H r : ℝ) / n r - parentMixture htotal n m mu r (pair a)| ≤ eps :=
    (htypical r (pair a)).le
  have hid : (Fintype.card {p : P // f p = a} : ℝ) / T -
      ∑ r, ((n r : ℝ) / T) * parentMixture htotal n m mu r (pair a) =
      ∑ r, ((n r : ℝ) / T) *
        ((H r : ℝ) / n r - parentMixture htotal n m mu r (pair a)) := by
    rw [hcount, Nat.cast_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hz : n r = 0
    · have hH : H r = 0 := by
        haveI : IsEmpty {t : Fin (n r) //
            ∀ h, pair (f (positions ⟨r,t⟩)) h = pair a h} :=
          ⟨fun t => by have ht := t.val.isLt; omega⟩
        exact Fintype.card_eq_zero
      simp only [H] at hH ⊢
      simp only [hz, hH, Nat.cast_zero, zero_div, zero_mul, sub_zero]
    · dsimp [H]
      field_simp [Nat.cast_ne_zero.mpr hz]
  rw [hid]
  calc
    _ ≤ ∑ r, |((n r : ℝ) / T) *
        ((H r : ℝ) / n r - parentMixture htotal n m mu r (pair a))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r, ((n r : ℝ) / T) * eps := by
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul, abs_of_nonneg (div_nonneg (hnr r) hTr.le)]
      exact mul_le_mul_of_nonneg_left (hlocal r) (div_nonneg (hnr r) hTr.le)
    _ = eps := by
      rw [← Finset.sum_mul, ← Finset.sum_div, ← Nat.cast_sum, hT,
        div_self hTr.ne', one_mul]




#print axioms solution
