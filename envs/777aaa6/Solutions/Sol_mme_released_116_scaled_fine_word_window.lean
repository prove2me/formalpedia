-- Prove2me | solution 1 for mme_released_116_scaled_fine_word_window
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T13:42:14.411745+00:00
-- url     : https://prove2.me/submissions/09780969-58b1-4b95-94de-f9a8fdcac737

import Definitions.Def_mme_recursive_profiled_CW_data
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FinCases
import Theorems.Thm_mme_released_116_regional_total
import Theorems.Thm_mme_released_116_regional_split_mass
import Theorems.Thm_mme_released_116_weighted_parent_center
import Definitions.Def_mme_released_116_integer_profiles
import Definitions.Def_mme_complete_split_concatenation
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Equiv.Fin.Basic

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open scoped Classical
set_option autoImplicit false

/-- A partition of physical parent positions splits a full-word histogram
into the exact pair-word histograms of its regions. -/
theorem mme_parent_histogram_sum_over_regions
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
the regional-size-weighted mean of their centers. -/
theorem mme_regional_parent_windows_imply_global_histogram_window
    {P A W : Type} [Fintype P] [Fintype W]
    {half R T : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ)
    (positions : (Σ r, Fin (n r)) ≃ P) (f : P → A)
    (pair : A ≃ (Fin 2 → W)) (eps : ℝ)
    (hn : ∀ r, 0 < n r) (hT : ∑ r, n r = T) (hTpos : 0 < T)
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
  have hnr (r : Fin R) : (0 : ℝ) < n r := by exact_mod_cast hn r
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
    dsimp [H]
    field_simp [(hnr r).ne']
  rw [hid]
  calc
    _ ≤ ∑ r, |((n r : ℝ) / T) *
        ((H r : ℝ) / n r - parentMixture htotal n m mu r (pair a))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r, ((n r : ℝ) / T) * eps := by
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul, abs_of_pos (div_pos (hnr r) hTr)]
      exact mul_le_mul_of_nonneg_left (hlocal r) (div_pos (hnr r) hTr).le
    _ = eps := by
      rw [← Finset.sum_mul, ← Finset.sum_div, ← Nat.cast_sum, hT,
        div_self hTr.ne', one_mul]


/-- Replicating every occurrence preserves each normalized child profile. -/
theorem mme_cell_frequency_scale
    {C W : Type*} [Fintype W] (mu : C → W → ℕ)
    (k : ℕ) (hk : 0 < k) (c : C) (w : W) :
    cellFrequency (fun c w => k * mu c w) c w = cellFrequency mu c w := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [cellFrequency, ← Finset.mul_sum, Nat.cast_mul]
  exact mul_div_mul_left _ _ hk'

/-- Uniform replication preserves the regional parent-mixture centers. -/
theorem mme_parent_mixture_scale
    {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ)
    (k : ℕ) (hk : 0 < k) (r : Fin R) (w : Fin 2 → W) :
    parentMixture htotal (fun r => k * n r) (fun r c => k * m r c)
      (fun c v => k * mu c v) r w = parentMixture htotal n m mu r w := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [parentMixture, mme_cell_frequency_scale mu k hk, Nat.cast_mul,
    mul_assoc, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hk'


open MME.Released116 MME.MoreAsymmetryExactSeed MME.CompleteSplit

/-- At every positive integer scale, the six regional windows imply a
full-word histogram window centered at the same released distribution. -/
theorem mme_released_116_scaled_partition_parent_window (k : ℕ) (hk : 0 < k) :
    ∃ positions : (Σ r : Fin 6, Fin (k * regionalSize r)) ≃
        Fin (k * denominator ^ 4),
      ∀ (i : Fin 3) (f : Fin (k * denominator ^ 4) → CompleteWord 3) (eps : ℝ),
        parentTypical parent_total (fun r => k * regionalSize r)
          (fun r c => k * splitCount r c) (fun c w => k * integerProfile i c w) eps
          (fun p =>
            let v := (completeWordSplitEquiv 2 (by decide)) (f (positions ⟨p.1,p.2.1⟩))
            ![v.1,v.2] p.2.2) →
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * denominator ^ 4) // f p = w} : ℝ) /
              (k * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows 0 10).map
              (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps := by
  classical
  have hT : (∑ r : Fin 6, k * regionalSize r) = k * denominator ^ 4 := by
    rw [← Finset.mul_sum, mme_released_116_regional_total]
  have hcard : Fintype.card (Σ r : Fin 6, Fin (k * regionalSize r)) =
      Fintype.card (Fin (k * denominator ^ 4)) := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using hT
  let positions := Fintype.equivOfCardEq hcard
  refine ⟨positions, ?_⟩
  intro i f eps htypical w
  let pair := (completeWordSplitEquiv 2 (by decide)).trans
    (finTwoArrowEquiv (CompleteWord 2)).symm
  have h := mme_regional_parent_windows_imply_global_histogram_window
    parent_total (fun r c => k * splitCount r c) (fun c w => k * integerProfile i c w)
    positions f pair eps
    (fun r => Nat.mul_pos hk (mme_released_116_regional_split_mass r).1)
    hT (Nat.mul_pos hk (by norm_num [denominator])) htypical w
  have hpair (v : CompleteWord 3) : pair v =
      ![((completeWordSplitEquiv 2 (by decide)) v).1,
        ((completeWordSplitEquiv 2 (by decide)) v).2] := rfl
  have hweight (r : Fin 6) :
      ((k * regionalSize r : ℕ) : ℝ) / (k * denominator ^ 4 : ℕ) =
        (regionalSize r : ℝ) / (denominator : ℝ) ^ 4 := by
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    simp only [Nat.cast_mul, Nat.cast_pow]
    exact mul_div_mul_left _ _ hk'
  simp only [mme_parent_mixture_scale _ _ _ _ k hk, hweight, hpair] at h
  rw [mme_released_116_weighted_parent_center i w] at h
  simp only [Fintype.card_eq_nat_card] at h ⊢
  exact h


/-- A partition of parent words induces a child-position order that agrees
with literal left/right splitting of the same fine word. -/
theorem mme_regional_parent_partition_fine_coordinates
    {R T : ℕ} {n : Fin R → ℕ}
    (positions : (Σ r, Fin (n r)) ≃ Fin T) :
    ∃ childPositions : Fin (T * 2) ≃ Position n,
      ∀ (x : ProfiledCW.FineWord (T * 4)) (p : Position n),
        ProfiledCW.split childPositions (show (T * 2) * 2 ^ (2 - 1) = T * 4 by omega) x p =
          (let v := completeWordSplitEquiv 2 (by decide)
            (ProfiledCW.split (Equiv.refl (Fin T)) rfl x (positions ⟨p.1,p.2.1⟩))
          ![v.1,v.2] p.2.2) := by
  let e : Fin (T * 2) ≃ Position n := finProdFinEquiv.symm.trans
    ((positions.symm.prodCongr (Equiv.refl (Fin 2))).trans
      (Equiv.sigmaProdDistrib (fun r => Fin (n r)) (Fin 2)))
  refine ⟨e, ?_⟩
  rintro x ⟨r,t,h⟩
  funext j
  fin_cases h <;> fin_cases j <;>
    simp [ProfiledCW.split, e, completeWordSplitEquiv, fineWordSplitEquiv,
      Equiv.sigmaProdDistrib, finProdFinEquiv, Nat.mul_add, ← Nat.mul_assoc, ← Nat.add_assoc]


/-- The scaled released histogram inclusion holds directly for the fine-word
splitting map required by an integer extraction step. -/
theorem solution (k : ℕ) (hk : 0 < k) :
    ∃ childPositions : Fin ((k * denominator ^ 4) * 2) ≃
        Position (fun r : Fin 6 => k * regionalSize r),
      ∀ (i : Fin 3) (x : ProfiledCW.FineWord ((k * denominator ^ 4) * 4)) (eps : ℝ),
        parentTypical parent_total (fun r => k * regionalSize r)
          (fun r c => k * splitCount r c) (fun c w => k * integerProfile i c w) eps
          (ProfiledCW.split childPositions
            (show ((k * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
              (k * denominator ^ 4) * 4 by omega) x) →
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * denominator ^ 4) //
              ProfiledCW.split (Equiv.refl (Fin (k * denominator ^ 4))) rfl x p = w} : ℝ) /
              (k * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows 0 10).map
              (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps := by
  classical
  obtain ⟨positions, hwindow⟩ := mme_released_116_scaled_partition_parent_window k hk
  obtain ⟨childPositions, hsplit⟩ := mme_regional_parent_partition_fine_coordinates positions
  refine ⟨childPositions, ?_⟩
  intro i x eps htypical w
  have hfun := funext (hsplit x)
  rw [hfun] at htypical
  exact hwindow i (ProfiledCW.split (Equiv.refl _) rfl x) eps htypical w

#print axioms solution
