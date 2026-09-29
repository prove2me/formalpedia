-- Prove2me | solution 1 for mme_released_116_parent_y_entropy_lower
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T00:03:41.355526+00:00
-- url     : https://prove2.me/submissions/168bd408-9bf5-4729-a7e2-b1524d0ed31a

import Theorems.Thm_mme_regional_mass_entropy_algebra
import Theorems.Thm_mme_released_116_regional_split_mass
import Definitions.Def_mme_regional_split_entropy_data

open BigOperators MME MME.RegionRate MME.RecursiveThinSplit
set_option autoImplicit false

/-- A tangent bound for the logarithm turns an atom-size bound into an entropy bound. -/
private theorem mme_entropy_lower_of_scaled_atom_bound {W : Type*} [Fintype W]
    (p : W → ℝ) (a b : ℝ) (ha : 0 < a) (hp : ∀ w, 0 ≤ p w)
    (hmass : ∑ w, p w = 1) (hbound : ∀ w, p w ≤ b) :
    Real.log a + 1 - a * b ≤ entropy p := by
  have hterm (w : W) : p w * (Real.log a + 1 - a * b) ≤
      Real.negMulLog (p w) := by
    by_cases hz : p w = 0
    · simp [hz]
    · have hpos := lt_of_le_of_ne (hp w) (Ne.symm hz)
      have hlog := Real.log_le_sub_one_of_pos (mul_pos ha hpos)
      rw [Real.log_mul ha.ne' hpos.ne'] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog (hp w)
      have hb := mul_le_mul_of_nonneg_left (hbound w) (mul_nonneg ha.le (hp w))
      rw [Real.negMulLog_def]
      nlinarith
  have h := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) => hterm w)
  simpa [entropy, ← Finset.sum_mul, hmass] using h

private abbrev Word := CompleteSplit.CompleteWord 2
private abbrev Split116 := Split 4 ![1, 1, 6]
private def c004 : Split116 := ⟨![0, 0, 4], by decide⟩
private def c013 : Split116 := ⟨![0, 1, 3], by decide⟩
private def c103 : Split116 := ⟨![1, 0, 3], by decide⟩
private def c112 : Split116 := ⟨![1, 1, 2], by decide⟩

private theorem split_univ : (Finset.univ : Finset Split116) = {c004, c013, c103, c112} := by
  decide

private theorem split_sum (f : Split116 → ℝ) :
    ∑ c, f c = f c004 + f c013 + f c103 + f c112 := by
  rw [split_univ]
  norm_num [c004, c013, c103, c112, add_assoc]

private def frequencyQ (i : Fin 3) (r : Fin 6) (c : Split116) (w : Word) : ℚ :=
  (Released116.integerProfile i ⟨r, c⟩ w : ℚ) /
    (∑ v : Word, Released116.integerProfile i ⟨r, c⟩ v : ℕ)

private def mixtureQ (i : Fin 3) (r : Fin 6) (w : Fin 2 → Word) : ℚ :=
  ((Released116.splitCount r c004 : ℚ) * frequencyQ i r c004 (w 0) * frequencyQ i r c112 (w 1) +
   (Released116.splitCount r c013 : ℚ) * frequencyQ i r c013 (w 0) * frequencyQ i r c103 (w 1) +
   (Released116.splitCount r c103 : ℚ) * frequencyQ i r c103 (w 0) * frequencyQ i r c013 (w 1) +
   (Released116.splitCount r c112 : ℚ) * frequencyQ i r c112 (w 0) * frequencyQ i r c004 (w 1)) /
    Released116.regionalSize r

private theorem frequencyQ_cast (i : Fin 3) (r : Fin 6) (c : Split116) (w : Word) :
    (frequencyQ i r c w : ℝ) = RegionRealization.cellFrequency
      (Released116.integerProfile i) ⟨r, c⟩ w := by
  simp [frequencyQ, RegionRealization.cellFrequency]

private theorem mixtureQ_cast (i : Fin 3) (r : Fin 6) (w : Fin 2 → Word) :
    (mixtureQ i r w : ℝ) = RegionRealization.parentMixture Released116.parent_total
      Released116.regionalSize Released116.splitCount (Released116.integerProfile i) r w := by
  unfold RegionRealization.parentMixture
  change _ = (∑ c : Split116, (Released116.splitCount r c : ℝ) *
    RegionRealization.cellFrequency (Released116.integerProfile i) ⟨r, c⟩ (w 0) *
    RegionRealization.cellFrequency (Released116.integerProfile i)
      ⟨r, RecursiveYZ.complement (Released116.parent_total r) c⟩ (w 1)) / _
  rw [split_sum]
  have h004 : RecursiveYZ.complement (Released116.parent_total r) c004 = c112 := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    fin_cases j <;> rfl
  have h013 : RecursiveYZ.complement (Released116.parent_total r) c013 = c103 := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    fin_cases j <;> rfl
  have h103 : RecursiveYZ.complement (Released116.parent_total r) c103 = c013 := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    fin_cases j <;> rfl
  have h112 : RecursiveYZ.complement (Released116.parent_total r) c112 = c004 := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    fin_cases j <;> rfl
  simp only [mixtureQ, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
    frequencyQ_cast, h004, h013, h103, h112]

private theorem mixtureQ_y_bounds : ∀ (r : Fin 6) (w : Fin 2 → Word),
    0 ≤ mixtureQ 1 r w ∧ mixtureQ 1 r w ≤ 250001 / 1000000 := by
  decide +kernel

private theorem mixtureQ_y_mass : ∀ r : Fin 6, ∑ w : Fin 2 → Word, mixtureQ 1 r w = 1 := by
  decide +kernel

private theorem mixtureQ_z_bounds : ∀ (r : Fin 6) (w : Fin 2 → Word),
    0 ≤ mixtureQ 2 r w ∧ mixtureQ 2 r w ≤ 193 / 1000 := by
  decide +kernel

private theorem mixtureQ_z_mass : ∀ r : Fin 6, ∑ w : Fin 2 → Word, mixtureQ 2 r w = 1 := by
  decide +kernel

private theorem parent_lower (i : Fin 3) (b : ℚ) (L : ℝ)
    (hbound : ∀ (r : Fin 6) (w : Fin 2 → Word), 0 ≤ mixtureQ i r w ∧ mixtureQ i r w ≤ b)
    (hmass : ∀ r : Fin 6, ∑ w : Fin 2 → Word, mixtureQ i r w = 1)
    (hlog : L ≤ Real.log 4 + 1 - 4 * (b : ℝ)) :
    L * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) ≤
      parentPotential Released116.parent_total Released116.regionalSize
        Released116.splitCount (Released116.integerProfile i) := by
  have hr (r : Fin 6) :
      L ≤ entropy (RegionRealization.parentMixture Released116.parent_total
        Released116.regionalSize Released116.splitCount (Released116.integerProfile i) r) := by
    apply hlog.trans
    apply mme_entropy_lower_of_scaled_atom_bound _ 4 (b : ℝ) (by norm_num)
    · intro w
      rw [← mixtureQ_cast]
      exact_mod_cast (hbound r w).1
    · simp_rw [← mixtureQ_cast]
      exact_mod_cast hmass r
    · intro w
      rw [← mixtureQ_cast]
      exact_mod_cast (hbound r w).2
  have h := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hr r) (Nat.cast_nonneg (Released116.regionalSize r)))
  rw [← Finset.sum_mul, ← Nat.cast_sum] at h
  simpa only [parentPotential, mul_comm L] using h

private theorem log_four : Real.log 4 = 2 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 2
  norm_num at h
  exact h

/-- The actual released Y parent mixtures have at least 1.38 natural-log entropy
per parent occurrence, certified from their exact rational atoms. -/
theorem solution :
    (138 / 100 : ℝ) * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) ≤
      parentPotential Released116.parent_total Released116.regionalSize
        Released116.splitCount (Released116.integerProfile 1) := by
  apply parent_lower 1 (250001 / 1000000) _ mixtureQ_y_bounds mixtureQ_y_mass
  rw [log_four]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have := Real.log_two_gt_d9
  linarith

/-- The actual released Z parent mixtures have at least 1.6 natural-log entropy
per parent occurrence, certified from their exact rational atoms. -/
private theorem mme_released_116_parent_z_entropy_lower :
    (160 / 100 : ℝ) * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) ≤
      parentPotential Released116.parent_total Released116.regionalSize
        Released116.splitCount (Released116.integerProfile 2) := by
  apply parent_lower 2 (193 / 1000) _ mixtureQ_z_bounds mixtureQ_z_mass
  rw [log_four]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have := Real.log_two_gt_d9
  linarith


#print axioms solution
