-- Prove2me | solution 1 for BookSixth.standard_pair_relabel_lt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T14:01:59.597569+00:00
-- url     : https://prove2.me/submissions/c902eb48-4344-4c8b-a481-4e2893621564

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_standard_pair_axis_homeo

open scoped BigOperators
open BookSixth

namespace PairAxisAdapter

noncomputable def lift (A : ℝ ≃ₜ ℝ) : Space3 ≃ₜ Space3 :=
  {
    toFun := fun x => ![A (x 0), x 1, x 2]
    invFun := fun y => ![A.symm (y 0), y 1, y 2]
    left_inv := by
      intro x
      funext k
      fin_cases k <;> simp
    right_inv := by
      intro y
      funext k
      fin_cases k <;> simp
    continuous_toFun := by
      apply continuous_pi
      intro k
      fin_cases k
      · exact A.continuous.comp (continuous_apply 0)
      · exact continuous_apply 1
      · exact continuous_apply 2
    continuous_invFun := by
      apply continuous_pi
      intro k
      fin_cases k
      · exact A.symm.continuous.comp (continuous_apply 0)
      · exact continuous_apply 1
      · exact continuous_apply 2
  }

end PairAxisAdapter

open PairAxisAdapter

theorem solution {i j : ℕ} (hij : i < j) :
    ∃ R : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => R p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (R p.1).symm p.2) ∧
      (∀ x, R 0 x = x) ∧
      (R 1) '' standardCircle i = standardCircle 0 ∧
      (R 1) '' standardCircle j = standardCircle 1 := by
  have hijR : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
  have hgap : (3 : ℝ) ≤ 3 * (j : ℝ) - 3 * (i : ℝ) := by
    have hba : (i : ℝ) + 1 ≤ (j : ℝ) := by
      exact_mod_cast (show i + 1 ≤ j by omega)
    norm_num at hba
    nlinarith
  obtain ⟨A, hAc, hAi, hA0, hAlo, hAhi⟩ :=
    BookSixth.standard_pair_axis_homeo
      (3 * (i : ℝ)) (3 * (j : ℝ))
      (by positivity) (by nlinarith [hijR]) hgap
  let R : ℝ → Space3 ≃ₜ Space3 := fun t => lift (A t)
  refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
  · apply continuous_pi
    intro k
    fin_cases k
    · change Continuous (fun p : ℝ × Space3 => A p.1 (p.2 0))
      exact hAc.comp
        (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))
    · change Continuous (fun p : ℝ × Space3 => p.2 1)
      exact (continuous_apply 1).comp continuous_snd
    · change Continuous (fun p : ℝ × Space3 => p.2 2)
      exact (continuous_apply 2).comp continuous_snd
  · apply continuous_pi
    intro k
    fin_cases k
    · change Continuous (fun p : ℝ × Space3 => (A p.1).symm (p.2 0))
      exact hAi.comp
        (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))
    · change Continuous (fun p : ℝ × Space3 => p.2 1)
      exact (continuous_apply 1).comp continuous_snd
    · change Continuous (fun p : ℝ × Space3 => p.2 2)
      exact (continuous_apply 2).comp continuous_snd
  · intro x
    funext k
    fin_cases k
    · change A 0 (x 0) = x 0
      rw [hA0]
    · rfl
    · rfl
  · have hlow (t : ℝ) :
        (R 1) ![3 * (i : ℝ) + Real.cos t, Real.sin t, 0] =
          ![3 * (0 : ℝ) + Real.cos t, Real.sin t, 0] := by
      funext k
      fin_cases k
      · change A 1 (3 * (i : ℝ) + Real.cos t) =
          3 * (0 : ℝ) + Real.cos t
        simpa using hAlo (Real.cos t)
          (Real.neg_one_le_cos t) (Real.cos_le_one t)
      · rfl
      · rfl
    unfold standardCircle
    apply Set.ext
    intro z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨t, rfl⟩ := hx
      exact ⟨t, by simpa using (hlow t).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨![3 * (i : ℝ) + Real.cos t, Real.sin t, 0],
        ⟨t, rfl⟩, by simpa using hlow t⟩
  · have hhigh (t : ℝ) :
        (R 1) ![3 * (j : ℝ) + Real.cos t, Real.sin t, 0] =
          ![3 * (1 : ℝ) + Real.cos t, Real.sin t, 0] := by
      funext k
      fin_cases k
      · change A 1 (3 * (j : ℝ) + Real.cos t) =
          3 * (1 : ℝ) + Real.cos t
        simpa using hAhi (Real.cos t)
          (Real.neg_one_le_cos t) (Real.cos_le_one t)
      · rfl
      · rfl
    unfold standardCircle
    apply Set.ext
    intro z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨t, rfl⟩ := hx
      exact ⟨t, by simpa using (hhigh t).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨![3 * (j : ℝ) + Real.cos t, Real.sin t, 0],
        ⟨t, rfl⟩, by simpa using hhigh t⟩
