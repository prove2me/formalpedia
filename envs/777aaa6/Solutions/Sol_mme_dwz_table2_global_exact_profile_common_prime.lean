-- Prove2me | solution 1 for mme_dwz_table2_global_exact_profile_common_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T23:26:26.329886+00:00
-- url     : https://prove2.me/submissions/1e58ffb3-a944-4d6d-bae4-8464106fe10d

import Theorems.Thm_mme_dwz_table2_exact_profile_coarse_Z_counts
import Theorems.Thm_mme_dwz_global_exact_profile_competitor_card_upper
import Theorems.Thm_mme_dwz_table2_outer_equiv_across_coarse_Z_words
import Theorems.Thm_mme_dwz_finite_candidate_family_common_prime_with_card_cap
import Theorems.Thm_mme_dwz_table2_exact_outer_profile_usefulBlock_nonempty
import Theorems.Thm_mme_dwz_table2_matchable_outer_family_component_words
import Theorems.Thm_mme_dwz_common_prime_le_exp_sixteen_length

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m d : ℕ) (hd : d ≤ 15 ^ (MME.DWZTable2Counts.scale * m)) :
    let L := MME.DWZTable2Counts.scale * m
    let ExactProfile : (Fin L → Fin 15) → Prop := fun w ↦
      ∀ s, Fintype.card {t : Fin L // w t = s} =
        MME.DWZTable2Counts.component s * m
    let T : Finset (Fin L → Fin 15) := by
      classical
      exact Finset.univ.filter ExactProfile
    let Owner := {w : Fin L → Fin 15 // ExactProfile w}
    ∃ base : Owner,
      let K₀ : Fin L → Fin 5 := fun t ↦
        MME.DWZSquare.shapeZ (base.1 t)
      let FixedOuter₀ :=
        {w : Fin L → Fin 15 //
          (∀ t, MME.DWZSquare.shapeZ (w t) = K₀ t) ∧ ExactProfile w}
      let R : ℝ :=
        (6 * (((L + 1 : ℕ) : ℝ))) ^ 9 *
          (Nat.card FixedOuter₀ : ℝ) *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              MME.DWZSquare.logAlphaP)
      let candidate : ∀ retained : Owner,
          MME.DWZTable2StandardForm.UsefulBlock m retained.1 →
            Finset (Fin L → Fin 15) := fun retained small ↦ by
        classical
        exact T.filter (fun w ↦
          (∀ t, MME.DWZSquare.shapeZ (w t) =
            MME.DWZSquare.shapeZ (retained.1 t)) ∧
          MME.DWZStep2Source.retainedFineCompatible m
            (fun w : Fin L → Fin 15 ↦ w)
            (fun t ↦ MME.DWZStep1Support.fineSplitGrade
              (small.1 t).1 (small.1 t).2) w)
      ∃ Q p : ℕ,
        (∀ retained small, (candidate retained small).card ≤ Q) ∧
        Q ≤ 15 ^ L ∧
        (Q : ℝ) ≤ R ∧
        p.Prime ∧ Odd p ∧ 4 < p ∧
        8 * d ≤ p ∧
        (∀ retained small, 8 * (candidate retained small).card ≤ p) ∧
        max 4 (8 * max d Q) < p ∧
        p ≤ 2 * max 4 (8 * max d Q) ∧
        (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R) ∧
        (p : ℝ) ≤ Real.exp (16 * (((L + 1 : ℕ) : ℝ))) := by
  classical
  dsimp only
  let L := MME.DWZTable2Counts.scale * m
  let ExactProfile : (Fin L → Fin 15) → Prop := fun w ↦
    ∀ s, Fintype.card {t : Fin L // w t = s} =
      MME.DWZTable2Counts.component s * m
  let T : Finset (Fin L → Fin 15) := Finset.univ.filter ExactProfile
  let Owner := {w : Fin L → Fin 15 // ExactProfile w}
  obtain ⟨K, _hK, hFixedOuter, _⟩ :=
    mme_dwz_table2_matchable_outer_family_component_words m
  obtain ⟨fixedBase⟩ := hFixedOuter
  let base : Owner := ⟨fixedBase.1, fixedBase.2.2⟩
  refine ⟨base, ?_⟩
  dsimp only
  let K₀ : Fin L → Fin 5 := fun t ↦
    MME.DWZSquare.shapeZ (base.1 t)
  let FixedOuter₀ :=
    {w : Fin L → Fin 15 //
      (∀ t, MME.DWZSquare.shapeZ (w t) = K₀ t) ∧ ExactProfile w}
  let R : ℝ :=
    (6 * (((L + 1 : ℕ) : ℝ))) ^ 9 *
      (Nat.card FixedOuter₀ : ℝ) *
      Real.exp
        ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
          MME.DWZSquare.logAlphaP)
  let candidate : ∀ retained : Owner,
      MME.DWZTable2StandardForm.UsefulBlock m retained.1 →
        Finset (Fin L → Fin 15) := fun retained small ↦
    T.filter (fun w ↦
      (∀ t, MME.DWZSquare.shapeZ (w t) =
        MME.DWZSquare.shapeZ (retained.1 t)) ∧
      MME.DWZStep2Source.retainedFineCompatible m
        (fun w : Fin L → Fin 15 ↦ w)
        (fun t ↦ MME.DWZStep1Support.fineSplitGrade
          (small.1 t).1 (small.1 t).2) w)
  let Block := Σ retained : Owner,
    MME.DWZTable2StandardForm.UsefulBlock m retained.1
  let candidates : (Fin L → Fin 15) → Block →
      Finset (Fin L → Fin 15) := fun _ block ↦
    candidate block.1 block.2
  letI : Nonempty Owner := ⟨base⟩
  letI : Nonempty Block := by
    let hsmall := mme_dwz_table2_exact_outer_profile_usefulBlock_nonempty
      m base.1 base.2
    exact hsmall.map fun small ↦ ⟨base, small⟩
  have hKbase : ∀ z,
      Fintype.card {t : Fin L // K₀ t = z} =
        MME.DWZTable2Counts.alphaZ z * m := by
    exact mme_dwz_table2_exact_profile_coarse_Z_counts m base.1 base.2
  have hfixedCard (retained : Owner) :
      Nat.card
          {w : Fin L → Fin 15 //
            (∀ t, MME.DWZSquare.shapeZ (w t) =
              MME.DWZSquare.shapeZ (retained.1 t)) ∧ ExactProfile w} =
        Nat.card FixedOuter₀ := by
    let K₁ : Fin L → Fin 5 := fun t ↦
      MME.DWZSquare.shapeZ (retained.1 t)
    have hK₁ : ∀ z,
        Fintype.card {t : Fin L // K₁ t = z} =
          MME.DWZTable2Counts.alphaZ z * m :=
      mme_dwz_table2_exact_profile_coarse_Z_counts m retained.1 retained.2
    obtain ⟨_e, _he, E, _hE⟩ :=
      mme_dwz_table2_outer_equiv_across_coarse_Z_words
        m K₁ K₀ hK₁ hKbase
    exact Nat.card_congr E
  have hR : ∀ retained block,
      (((candidates retained block).card : ℕ) : ℝ) ≤ R := by
    intro _ block
    simp only [candidates]
    have hbound :=
      mme_dwz_global_exact_profile_competitor_card_upper
        m T (by
          intro w hw
          exact (Finset.mem_filter.mp hw).2)
        block.1.1
        (mme_dwz_table2_exact_profile_coarse_Z_counts
          m block.1.1 block.1.2)
        block.2
    have hbound' := hbound
    dsimp only at hbound'
    have hfixedCard' :
        Nat.card
            {w : Fin L → Fin 15 //
              (∀ t, MME.DWZSquare.shapeZ (w t) =
                MME.DWZSquare.shapeZ (block.1.1 t)) ∧
              ∀ s, Fintype.card {t : Fin L // w t = s} =
                MME.DWZTable2Counts.component s * m} =
          Nat.card FixedOuter₀ := by
      simpa only [ExactProfile] using hfixedCard block.1
    rw [hfixedCard'] at hbound'
    convert hbound' using 1
    simp only [candidate, L]
    norm_cast
    apply congrArg Finset.card
    ext w
    simp only [Finset.mem_filter]
  obtain ⟨Q, p, hcard, hQambient, hQR, hp, hpodd, hp4, hdp,
      hbudget, hpLower, hpUpper, hpR⟩ :=
    mme_dwz_finite_candidate_family_common_prime_with_card_cap
      candidates d R hR
  have hQpow : Q ≤ 15 ^ L := by
    calc
      Q ≤ Fintype.card (Fin L → Fin 15) := hQambient
      _ = 15 ^ L := by simp
  have hpExp : (p : ℝ) ≤ Real.exp (16 * (((L + 1 : ℕ) : ℝ))) :=
    mme_dwz_common_prime_le_exp_sixteen_length L d Q p hd hQpow hpUpper
  refine ⟨Q, p, ?_, hQpow, hQR, hp, hpodd, hp4, hdp, ?_,
    hpLower, hpUpper, hpR, hpExp⟩
  · intro retained small
    simpa only [candidates] using
      hcard retained.1 (Sigma.mk retained small)
  · intro retained small
    simpa only [candidates] using
      hbudget retained.1 (Sigma.mk retained small)
