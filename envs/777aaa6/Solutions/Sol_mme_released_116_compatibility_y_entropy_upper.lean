-- Prove2me | solution 1 for mme_released_116_compatibility_y_entropy_upper
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T00:08:48.873081+00:00
-- url     : https://prove2.me/submissions/d5555972-cb05-4fbe-94a5-e500a3aaa562

import Theorems.Thm_mme_regional_mass_entropy_algebra
import Theorems.Thm_mme_released_116_integer_profile_support

open BigOperators MME.RegionRate
set_option autoImplicit false

/-- A probability distribution supported on at most k atoms has entropy at most log k. -/
private theorem mme_entropy_upper_of_support_card {W : Type*} [Fintype W]
    (p : W → ℝ) (S : Finset W) (k : ℕ) (hk : 0 < k)
    (hp : ∀ w, 0 ≤ p w) (hmass : ∑ w, p w = 1)
    (hsupp : ∀ w, w ∉ S → p w = 0) (hcard : S.card ≤ k) :
    entropy p ≤ Real.log k := by
  classical
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hterm (w : W) : Real.negMulLog (p w) ≤
      p w * Real.log k + (k : ℝ)⁻¹ - p w := by
    by_cases hz : p w = 0
    · simp [hz, inv_nonneg.mpr hk'.le]
    · have hpos := lt_of_le_of_ne (hp w) (Ne.symm hz)
      have hlog := Real.log_le_sub_one_of_pos (div_pos (inv_pos.mpr hk') hpos)
      rw [Real.log_div (inv_ne_zero hk'.ne') hz, Real.log_inv] at hlog
      have h := mul_le_mul_of_nonneg_left hlog (hp w)
      have he : p w * ((k : ℝ)⁻¹ / p w) = (k : ℝ)⁻¹ := by field_simp
      simp only [mul_sub, he, mul_one] at h
      rw [Real.negMulLog_def]
      nlinarith
  have hmassS : ∑ w ∈ S, p w = 1 := by
    rw [← hmass]
    exact Finset.sum_subset (Finset.subset_univ _) (fun w _ hw => hsupp w hw)
  have hsum : entropy p = ∑ w ∈ S, Real.negMulLog (p w) := by
    unfold entropy
    exact (Finset.sum_subset (Finset.subset_univ _) (fun w _ hw => by simp [hsupp w hw])).symm
  rw [hsum]
  have h := Finset.sum_le_sum (fun w (_ : w ∈ S) => hterm w)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    hmassS, one_mul, Finset.sum_const, nsmul_eq_mul] at h
  have hc : (S.card : ℝ) * (k : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hk']
    exact_mod_cast hcard
  linarith

/-- Homogeneous entropy obeys the same support-cardinality bound, including empty histograms. -/
private theorem mme_mass_entropy_upper_of_support_card {W : Type*} [Fintype W]
    (mu : W → ℕ) (S : Finset W) (k : ℕ) (hk : 0 < k)
    (hsupp : ∀ w, w ∉ S → mu w = 0) (hcard : S.card ≤ k) :
    massEntropy (fun w => (mu w : ℝ)) ≤ ((∑ w, mu w : ℕ) : ℝ) * Real.log k := by
  classical
  by_cases hz : ∑ w, mu w = 0
  · have hw : ∀ w, mu w = 0 := fun w => Finset.sum_eq_zero_iff.mp hz w (Finset.mem_univ _)
    simp [hw, massEntropy, entropy]
  · have hs : (∑ w, (mu w : ℝ)) ≠ 0 := by exact_mod_cast hz
    rw [(mme_regional_mass_entropy_algebra (C := Unit) (W := W)).2.1 _ hs]
    simp only [← Nat.cast_sum]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply mme_entropy_upper_of_support_card _ S k hk
    · intro w; positivity
    · rw [← Finset.sum_div, ← Nat.cast_sum, div_self (by exact_mod_cast hz)]
    · intro w hw; simp [hsupp w hw]
    · exact hcard


private abbrev Word := MME.CompleteSplit.CompleteWord 2
private def gradeSupport (j : Fin 5) : Finset Word :=
  Finset.univ.filter (fun w => ∑ h, (w h).val = j.val)

private theorem grade_card : ∀ j : Fin 5,
    (gradeSupport j).card ≤ 2 ^ j.val ∧ (gradeSupport j).card ≤ 2 ^ (4 - j.val) := by
  decide +kernel

private theorem grade_entropy_upper (mu : Word → ℕ) (j : Fin 5)
    (hsupp : ∀ w, 0 < mu w → ∑ h, (w h).val = j.val) (d : ℕ)
    (hcard : (gradeSupport j).card ≤ 2 ^ d) :
    massEntropy (fun w => (mu w : ℝ)) ≤ ((∑ w, mu w : ℕ) : ℝ) * d * Real.log 2 := by
  have h := mme_mass_entropy_upper_of_support_card mu (gradeSupport j) (2 ^ d)
    (by positivity) (fun w hw => by
      by_contra hn
      have hg := hsupp w (Nat.pos_of_ne_zero hn)
      exact hw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)) hcard
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, mul_assoc] using h

/-- A two-symbol child histogram of grade j has at most 2^j possible words. -/
private theorem mme_complete_word_two_low_grade_entropy_upper
    (mu : MME.CompleteSplit.CompleteWord 2 → ℕ) (j : Fin 5)
    (hsupp : ∀ w, 0 < mu w → ∑ h, (w h).val = j.val) :
    massEntropy (fun w => (mu w : ℝ)) ≤ ((∑ w, mu w : ℕ) : ℝ) * j.val * Real.log 2 := by
  exact grade_entropy_upper mu j hsupp j.val (grade_card j).1

/-- Reversing the word grades gives the sharper bound for high-grade children. -/
private theorem mme_complete_word_two_high_grade_entropy_upper
    (mu : MME.CompleteSplit.CompleteWord 2 → ℕ) (j : Fin 5)
    (hsupp : ∀ w, 0 < mu w → ∑ h, (w h).val = j.val) :
    massEntropy (fun w => (mu w : ℝ)) ≤ ((∑ w, mu w : ℕ) : ℝ) * (4 - j.val : ℕ) * Real.log 2 := by
  exact grade_entropy_upper mu j hsupp (4 - j.val) (grade_card j).2

open MME.RecursiveYZ
open scoped Classical

private theorem part_weighted_count {C W G : Type*} [Fintype C] [Fintype G]
    (boundary : C → Prop) (group : C → G) (mu : C → W → ℕ) (d : G → ℕ) (w : W) :
    ∑ s : {c : C // boundary c} ⊕ G,
      partCount boundary group mu s w * (s.elim (fun c => d (group c.val)) d) =
        ∑ c, mu c w * d (group c) := by
  simp only [Fintype.sum_sum_type, partCount, Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.sum_subtype (Finset.univ.filter boundary) (fun c => by simp)
    (fun c => mu c w * d (group c)), Finset.sum_filter]
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : boundary c <;> simp [hc]

private theorem part_weighted_mass {C W G : Type*} [Fintype C] [Fintype G] [Fintype W]
    (boundary : C → Prop) (group : C → G) (mu : C → W → ℕ) (d : G → ℕ) :
    ∑ s : {c : C // boundary c} ⊕ G,
      (∑ w, partCount boundary group mu s w) * (s.elim (fun c => d (group c.val)) d) =
        ∑ c, (∑ w, mu c w) * d (group c) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [part_weighted_count]
  rw [Finset.sum_comm]

open MME

private abbrev Parts (i : Fin 2) :=
  {c : Cell 4 6 Released116.parent // yzBoundary i c} ⊕ (Fin 6 × Fin 5)

private def partGrade (i : Fin 2) (s : Parts i) : Fin 5 :=
  s.elim (fun c => c.val.2.val (yzMode i)) Prod.snd

private theorem part_support (i : Fin 2) (s : Parts i) (w : Word)
    (h : 0 < partCount (yzBoundary i) (modeGroup (yzMode i))
      (Released116.integerProfile (yzMode i)) s w) :
    ∑ a, (w a).val = (partGrade i s).val := by
  cases s with
  | inl c => exact mme_released_116_integer_profile_support (yzMode i) c.val w h
  | inr g =>
    dsimp [partCount] at h
    obtain ⟨c, _, hc⟩ := Finset.sum_pos_iff.mp h
    split_ifs at hc with hcg
    · have hs := mme_released_116_integer_profile_support (yzMode i) c w hc
      have hg := congrArg (fun t : Fin 6 × Fin 5 => t.2.val) hcg.2
      exact hs.trans hg
    · omega

private theorem released_weighted_y_mass :
    ∑ c : Cell 4 6 Released116.parent,
      (∑ w, Released116.integerProfile 1 c w) * (modeGroup 1 c).2.val =
        ∑ r, Released116.regionalSize r := by
  decide +kernel

private theorem released_weighted_z_mass :
    ∑ c : Cell 4 6 Released116.parent,
      (∑ w, Released116.integerProfile 2 c w) * (4 - (modeGroup 2 c).2.val) =
        2 * ∑ r, Released116.regionalSize r := by
  decide +kernel

/-- The compatibility partition retains Y grades, whose total is one per parent. -/
theorem solution :
    compatibilityPotential 0 (Released116.integerProfile 1) ≤
      ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) * Real.log 2 := by
  unfold compatibilityPotential
  rw [(mme_regional_mass_entropy_algebra (C := Parts 0) (W := Word)).2.2]
  have h := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
    mme_complete_word_two_low_grade_entropy_upper
      (partCount (yzBoundary 0) (modeGroup (yzMode 0))
        (Released116.integerProfile (yzMode 0)) s)
      (partGrade 0 s) (part_support 0 s))
  refine h.trans_eq ?_
  rw [← Finset.sum_mul]
  have hm := part_weighted_mass (yzBoundary (half := 4) (parent := Released116.parent) 0)
    (modeGroup (yzMode 0)) (Released116.integerProfile (yzMode 0)) (fun g => g.2.val)
  have he (s : Parts 0) :
      s.elim (fun c => (modeGroup (yzMode 0) c.val).2.val) (fun g => g.2.val) =
        (partGrade 0 s).val := by cases s <;> rfl
  simp only [he] at hm
  have ht : (∑ s : Parts 0, (∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0))
    (Released116.integerProfile (yzMode 0)) s w) * (partGrade 0 s).val) =
      ∑ r, Released116.regionalSize r := hm.trans released_weighted_y_mass
  congr 1
  exact_mod_cast ht

/-- The complementary Z grade totals two per parent, bounding compatibility entropy. -/
private theorem mme_released_116_compatibility_z_entropy_upper :
    compatibilityPotential 1 (Released116.integerProfile 2) ≤
      (2 * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ)) * Real.log 2 := by
  unfold compatibilityPotential
  rw [(mme_regional_mass_entropy_algebra (C := Parts 1) (W := Word)).2.2]
  have h := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
    mme_complete_word_two_high_grade_entropy_upper
      (partCount (yzBoundary 1) (modeGroup (yzMode 1))
        (Released116.integerProfile (yzMode 1)) s)
      (partGrade 1 s) (part_support 1 s))
  refine h.trans_eq ?_
  rw [← Finset.sum_mul]
  have hm := part_weighted_mass (yzBoundary (half := 4) (parent := Released116.parent) 1)
    (modeGroup (yzMode 1)) (Released116.integerProfile (yzMode 1)) (fun g => 4 - g.2.val)
  have he (s : Parts 1) :
      s.elim (fun c => 4 - (modeGroup (yzMode 1) c.val).2.val) (fun g => 4 - g.2.val) =
        4 - (partGrade 1 s).val := by cases s <;> rfl
  simp only [he] at hm
  have ht : (∑ s : Parts 1, (∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1))
    (Released116.integerProfile (yzMode 1)) s w) * (4 - (partGrade 1 s).val)) =
      2 * ∑ r, Released116.regionalSize r := hm.trans released_weighted_z_mass
  congr 1
  exact_mod_cast ht


#print axioms solution
