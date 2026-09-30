-- Prove2me | solution 1 for Hirsch.irredundant_rows_card_le_any_equivalent_presentation
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T03:46:22.583267+00:00
-- url     : https://prove2.me/submissions/9194432c-54e2-4e6a-9aaf-d7c27fb9934e

import Definitions.Def_Hirsch_circuit_model

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped RealInnerProductSpace
open Hirsch

namespace HirschRowCountStandalone

private theorem irredundant_rows_nonzero_of_mem
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hirr : RowPresentationIrredundant a b)
    (x₀ : EuclideanSpace ℝ (Fin d)) (hx₀ : x₀ ∈ Hpoly a b) :
    ∀ i : Fin n, a i ≠ 0 := by
  intro i hi0
  obtain ⟨x, _hx, hxi⟩ := hirr i
  have hi := hx₀ i
  rw [hi0, inner_zero_left] at hxi hi
  linarith

private theorem exists_pos_mul_abs_lt
    {ι : Type*} (S : Finset ι) (c r : ι → ℝ) :
    (∀ i ∈ S, 0 < r i) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ S, ε * |c i| < r i := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨1, by norm_num, ?_⟩
      simp
  | @insert i S hi ih =>
      intro hr
      obtain ⟨ε, hε, hS⟩ := ih (fun j hj => hr j (Finset.mem_insert_of_mem hj))
      have hri : 0 < r i := hr i (Finset.mem_insert_self i S)
      have hden : 0 < |c i| + 1 := by positivity
      let δ : ℝ := min ε (r i / (|c i| + 1))
      have hδ : 0 < δ := lt_min hε (div_pos hri hden)
      have hδε : δ ≤ ε := min_le_left _ _
      have hδr : δ * (|c i| + 1) ≤ r i :=
        (le_div_iff₀ hden).mp (min_le_right _ _)
      refine ⟨δ / 2, by positivity, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjS
      · subst j
        nlinarith [abs_nonneg (c i)]
      · calc
          (δ / 2) * |c j| ≤ ε * |c j| :=
            mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg (c j))
          _ < r j := hS j hjS

private theorem strict_on_nonzero_rows_strict_for_valid_row
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b)
    (hstrict : ∀ i, a i ≠ 0 → ⟪a i, x⟫ < b i)
    (c : EuclideanSpace ℝ (Fin d)) (β : ℝ) (hc : c ≠ 0)
    (hvalid : ∀ y, y ∈ Hpoly a b → ⟪c, y⟫ ≤ β) :
    ⟪c, x⟫ < β := by
  classical
  have hxβ : ⟪c, x⟫ ≤ β := hvalid x hx
  by_contra hnot
  have heq : ⟪c, x⟫ = β := le_antisymm hxβ (le_of_not_gt hnot)
  let S : Finset (Fin n) := Finset.univ.filter (fun i => a i ≠ 0)
  obtain ⟨ε, hε, hsmall⟩ := exists_pos_mul_abs_lt S
    (fun i => ⟪a i, c⟫) (fun i => b i - ⟪a i, x⟫)
    (by
      intro i hi
      exact sub_pos.mpr (hstrict i (Finset.mem_filter.mp hi).2))
  have hy : x + ε • c ∈ Hpoly a b := by
    intro i
    by_cases hai : a i = 0
    · simpa only [hai, inner_zero_left] using hx i
    · have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hai⟩
      have hb := hsmall i hiS
      have habs : ε * ⟪a i, c⟫ ≤ ε * |⟪a i, c⟫| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hε.le
      simp only [inner_add_right, inner_smul_right]
      linarith
  have hcc : 0 < ⟪c, c⟫ := by
    rw [real_inner_self_eq_norm_mul_norm]
    exact mul_pos (norm_pos_iff.mpr hc) (norm_pos_iff.mpr hc)
  have hyβ := hvalid (x + ε • c) hy
  simp only [inner_add_right, inner_smul_right] at hyβ
  have hpos := mul_pos hε hcc
  linarith

private theorem exists_nonzero_tight_row_of_valid_tight_row
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b)
    (c : EuclideanSpace ℝ (Fin d)) (β : ℝ) (hc : c ≠ 0)
    (hvalid : ∀ y, y ∈ Hpoly a b → ⟪c, y⟫ ≤ β)
    (htight : ⟪c, x⟫ = β) :
    ∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, x⟫ = b i := by
  classical
  by_contra hnone
  have hs : ∀ i, a i ≠ 0 → ⟪a i, x⟫ < b i := by
    intro i hai
    have hne : ⟪a i, x⟫ ≠ b i := by
      intro heq
      exact hnone ⟨i, hai, heq⟩
    exact lt_of_le_of_ne (hx i) hne
  have hlt := strict_on_nonzero_rows_strict_for_valid_row a b x hx hs c β hc hvalid
  linarith

private theorem exists_single_tight_point_of_irredundant
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hirr : RowPresentationIrredundant a b)
    (hstrict : StrictlyFeasibleRows a b) (i : Fin n) :
    ∃ x : EuclideanSpace ℝ (Fin d),
      ⟪a i, x⟫ = b i ∧ ∀ j : Fin n, j ≠ i → ⟪a j, x⟫ < b j := by
  obtain ⟨c, hc⟩ := hstrict
  obtain ⟨w, hw, hwi⟩ := hirr i
  have hden : 0 < ⟪a i, w⟫ - ⟪a i, c⟫ := by linarith [hc i]
  let t : ℝ := (b i - ⟪a i, c⟫) / (⟪a i, w⟫ - ⟪a i, c⟫)
  have ht0 : 0 < t := div_pos (sub_pos.mpr (hc i)) hden
  have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
  have hmul : t * (⟪a i, w⟫ - ⟪a i, c⟫) = b i - ⟪a i, c⟫ := by
    dsimp [t]
    exact div_mul_cancel₀ _ (ne_of_gt hden)
  refine ⟨(1 - t) • c + t • w, ?_, ?_⟩
  · simp only [inner_add_right, inner_smul_right]
    nlinarith [hmul]
  · intro j hji
    have hleft : 0 < (1 - t) * (b j - ⟪a j, c⟫) :=
      mul_pos (sub_pos.mpr ht1) (sub_pos.mpr (hc j))
    have hright : 0 ≤ t * (b j - ⟪a j, w⟫) :=
      mul_nonneg ht0.le (sub_nonneg.mpr (hw j hji))
    simp only [inner_add_right, inner_smul_right]
    nlinarith [hleft, hright]

end HirschRowCountStandalone

open HirschRowCountStandalone

/-- A strictly feasible irredundant finite H-presentation is globally
cardinality-minimal among all equivalent finite H-presentations. -/
theorem solution
    {d n m : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : Fin m → EuclideanSpace ℝ (Fin d)) (β : Fin m → ℝ)
    (hirr : RowPresentationIrredundant a b)
    (hstrict : StrictlyFeasibleRows a b)
    (hP : Hpoly c β = Hpoly a b) : n ≤ m := by
  classical
  obtain ⟨z, hz⟩ := hstrict
  have hzP : z ∈ Hpoly a b := fun i => (hz i).le
  have ha0 := irredundant_rows_nonzero_of_mem a b hirr z hzP
  choose p htight hsingle using
    exists_single_tight_point_of_irredundant a b hirr ⟨z, hz⟩
  have hp : ∀ i, p i ∈ Hpoly a b := by
    intro i j
    by_cases hji : j = i
    · subst j
      exact (htight i).le
    · exact (hsingle i j hji).le
  have hblock : ∀ i : Fin n, ∃ j : Fin m, c j ≠ 0 ∧ ⟪c j, p i⟫ = β j := by
    intro i
    apply exists_nonzero_tight_row_of_valid_tight_row c β (p i)
      (by rw [hP]; exact hp i) (a i) (b i) (ha0 i)
    · intro y hy
      have hyA : y ∈ Hpoly a b := by rw [← hP]; exact hy
      exact hyA i
    · exact htight i
  choose f hf0 hftight using hblock
  have hfinj : Function.Injective f := by
    intro i k hfik
    by_contra hik
    let q : EuclideanSpace ℝ (Fin d) :=
      (1 / 2 : ℝ) • p i + (1 / 2 : ℝ) • p k
    have hqs : ∀ j : Fin n, ⟪a j, q⟫ < b j := by
      intro j
      have hji := hp i j
      have hjk := hp k j
      have hsome : ⟪a j, p i⟫ < b j ∨ ⟪a j, p k⟫ < b j := by
        by_cases hjeq : j = i
        · right
          apply hsingle k j
          intro hjk_eq
          exact hik (hjeq.symm.trans hjk_eq)
        · exact Or.inl (hsingle i j hjeq)
      dsimp [q]
      simp only [inner_add_right, inner_smul_right]
      rcases hsome with hlt | hlt <;> linarith
    have hqP : q ∈ Hpoly a b := fun j => (hqs j).le
    have hqstrict := strict_on_nonzero_rows_strict_for_valid_row a b q hqP
      (fun j _ => hqs j) (c (f i)) (β (f i)) (hf0 i)
      (by
        intro y hy
        have hyC : y ∈ Hpoly c β := by rw [hP]; exact hy
        exact hyC (f i))
    have hti := hftight i
    have htk : ⟪c (f i), p k⟫ = β (f i) := by
      simpa only [hfik] using hftight k
    dsimp [q] at hqstrict
    simp only [inner_add_right, inner_smul_right] at hqstrict
    linarith
  have hcard := Fintype.card_le_of_injective f hfinj
  simpa only [Fintype.card_fin] using hcard

#print axioms solution
