-- Prove2me | solution 1 for mme_CW_2376_exact_profile_address_marginals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T19:38:36.67451+00:00
-- url     : https://prove2.me/submissions/cc94993c-3b42-433a-bf10-bcc8ec74a2d3

import Definitions.Def_mme_CW_2376_profile_induced_family

open MME BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1600000

@[simp] private theorem cwSquareBlockType_eq_iff
    (I J K I' J' K' : Fin 5) :
    cwSquareBlockType I J K = cwSquareBlockType I' J' K' ↔
      I = I' ∧ J = J' ∧ K = K' := by
  constructor
  · intro h
    have h0 := congrFun h (0 : Fin 3)
    have h1 := congrFun h (1 : Fin 3)
    have h2 := congrFun h (2 : Fin 3)
    simpa [cwSquareBlockType] using And.intro h0 (And.intro h1 h2)
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private theorem exactProfile_marginal_count
    (m : ℕ) (a : CW2376ExactProfileAddress m)
    (i : Fin 3) (r : Fin 5) :
    (Finset.univ.filter (fun j => a.1 i j = r)).card =
      ∑ σ ∈ (Finset.univ.filter (fun σ : Fin 3 → Fin 5 => σ i = r)),
        cw2376ProfileMultiplicity m σ := by
  let types : Finset (Fin 3 → Fin 5) :=
    Finset.univ.filter (fun σ => σ i = r)
  calc
    (Finset.univ.filter (fun j => a.1 i j = r)).card =
        (Finset.univ.filter (fun j =>
          cw2376AddressType a.1 j ∈ types)).card := by
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        types, cw2376AddressType]
    _ = ∑ σ ∈ types,
        (Finset.univ.filter
          (fun j => cw2376AddressType a.1 j = σ)).card := by
      exact (Finset.sum_card_fiberwise_eq_card_filter
        Finset.univ types (cw2376AddressType a.1)).symm
    _ = ∑ σ ∈ types, cw2376ProfileMultiplicity m σ := by
      apply Finset.sum_congr rfl
      intro σ _
      exact a.2 σ
    _ = ∑ σ ∈ (Finset.univ.filter
          (fun σ : Fin 3 → Fin 5 => σ i = r)),
        cw2376ProfileMultiplicity m σ := by rfl

private def expectedMarginalMultiplicity (m : ℕ) : Fin 5 → ℕ
  | ⟨0, _⟩ => 384072 * m
  | ⟨1, _⟩ => 1308290 * m
  | ⟨2, _⟩ => 1231903 * m
  | ⟨3, _⟩ => 75036 * m
  | ⟨4, _⟩ => 699 * m

private theorem profileMultiplicity_of_mem_scalar
    (m : ℕ) {σ : Fin 3 → Fin 5} (hσ : σ ∈ cw2376ScalarTypes) :
    cw2376ProfileMultiplicity m σ = 699 * m := by
  simp [cw2376ProfileMultiplicity, hσ]

private theorem profileMultiplicity_of_mem_rect
    (m : ℕ) {σ : Fin 3 → Fin 5} (hσ : σ ∈ cw2376RectTypes) :
    cw2376ProfileMultiplicity m σ = 37518 * m := by
  have hnotScalar : σ ∉ cw2376ScalarTypes := by
    intro hs
    exact Finset.disjoint_left.mp
      (show Disjoint cw2376ScalarTypes cw2376RectTypes from by decide) hs hσ
  simp [cw2376ProfileMultiplicity, hnotScalar, hσ]

private theorem profileMultiplicity_of_mem_central
    (m : ℕ) {σ : Fin 3 → Fin 5} (hσ : σ ∈ cw2376CentralTypes) :
    cw2376ProfileMultiplicity m σ = 307638 * m := by
  have hnotScalar : σ ∉ cw2376ScalarTypes := by
    intro hs
    exact Finset.disjoint_left.mp
      (show Disjoint cw2376ScalarTypes cw2376CentralTypes from by decide) hs hσ
  have hnotRect : σ ∉ cw2376RectTypes := by
    intro hr
    exact Finset.disjoint_left.mp
      (show Disjoint cw2376RectTypes cw2376CentralTypes from by decide) hr hσ
  simp [cw2376ProfileMultiplicity, hnotScalar, hnotRect, hσ]

private theorem profileMultiplicity_of_mem_coupled
    (m : ℕ) {σ : Fin 3 → Fin 5} (hσ : σ ∈ cw2376CoupledTypes) :
    cw2376ProfileMultiplicity m σ = 616627 * m := by
  have hnotScalar : σ ∉ cw2376ScalarTypes := by
    intro hs
    exact Finset.disjoint_left.mp
      (show Disjoint cw2376ScalarTypes cw2376CoupledTypes from by decide) hs hσ
  have hnotRect : σ ∉ cw2376RectTypes := by
    intro hr
    exact Finset.disjoint_left.mp
      (show Disjoint cw2376RectTypes cw2376CoupledTypes from by decide) hr hσ
  have hnotCentral : σ ∉ cw2376CentralTypes := by
    intro hc
    exact Finset.disjoint_left.mp
      (show Disjoint cw2376CentralTypes cw2376CoupledTypes from by decide) hc hσ
  simp [cw2376ProfileMultiplicity, hnotScalar, hnotRect, hnotCentral, hσ]

private def scalarMarginalCard : Fin 5 → ℕ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => 0
  | ⟨4, _⟩ => 1

private def rectMarginalCard : Fin 5 → ℕ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 0

private def centralMarginalCard : Fin 5 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 0
  | ⟨4, _⟩ => 0

private def coupledMarginalCard : Fin 5 → ℕ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 0
  | ⟨4, _⟩ => 0

private theorem scalar_filter_card (i : Fin 3) (r : Fin 5) :
    (cw2376ScalarTypes.filter (fun σ => σ i = r)).card =
      scalarMarginalCard r := by
  fin_cases i <;> fin_cases r <;> decide

private theorem rect_filter_card (i : Fin 3) (r : Fin 5) :
    (cw2376RectTypes.filter (fun σ => σ i = r)).card =
      rectMarginalCard r := by
  fin_cases i <;> fin_cases r <;> decide

private theorem central_filter_card (i : Fin 3) (r : Fin 5) :
    (cw2376CentralTypes.filter (fun σ => σ i = r)).card =
      centralMarginalCard r := by
  fin_cases i <;> fin_cases r <;> decide

private theorem coupled_filter_card (i : Fin 3) (r : Fin 5) :
    (cw2376CoupledTypes.filter (fun σ => σ i = r)).card =
      coupledMarginalCard r := by
  fin_cases i <;> fin_cases r <;> decide

private theorem profileMultiplicity_sum_marginal
    (m : ℕ) (i : Fin 3) (r : Fin 5) :
    (∑ σ ∈ (Finset.univ.filter
        (fun σ : Fin 3 → Fin 5 => σ i = r)),
      cw2376ProfileMultiplicity m σ) =
        expectedMarginalMultiplicity m r := by
  let S : Finset (Fin 3 → Fin 5) :=
    cw2376ScalarTypes ∪ cw2376RectTypes ∪
      cw2376CentralTypes ∪ cw2376CoupledTypes
  have hsubset : S.filter (fun σ => σ i = r) ⊆
      (Finset.univ.filter (fun σ : Fin 3 → Fin 5 => σ i = r)) := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact hσ.2
  have hzero : ∀ σ ∈ (Finset.univ.filter
        (fun σ : Fin 3 → Fin 5 => σ i = r)),
      σ ∉ S.filter (fun σ => σ i = r) →
        cw2376ProfileMultiplicity m σ = 0 := by
    intro σ hmem hfiltered
    have hσ : σ ∉ S := by
      intro hs
      apply hfiltered
      exact Finset.mem_filter.mpr ⟨hs, (Finset.mem_filter.mp hmem).2⟩
    have hs : σ ∉ cw2376ScalarTypes := by
      intro h
      exact hσ (by simp [S, h])
    have hr : σ ∉ cw2376RectTypes := by
      intro h
      exact hσ (by simp [S, h])
    have hc : σ ∉ cw2376CentralTypes := by
      intro h
      exact hσ (by simp [S, h])
    have hd : σ ∉ cw2376CoupledTypes := by
      intro h
      exact hσ (by simp [S, h])
    simp [cw2376ProfileMultiplicity, hs, hr, hc, hd]
  rw [← Finset.sum_subset hsubset hzero]
  have hSR : Disjoint cw2376ScalarTypes cw2376RectTypes := by decide
  have hSC : Disjoint cw2376ScalarTypes cw2376CentralTypes := by decide
  have hSD : Disjoint cw2376ScalarTypes cw2376CoupledTypes := by decide
  have hRC : Disjoint cw2376RectTypes cw2376CentralTypes := by decide
  have hRD : Disjoint cw2376RectTypes cw2376CoupledTypes := by decide
  have hCD : Disjoint cw2376CentralTypes cw2376CoupledTypes := by decide
  have hSRC : Disjoint
      (cw2376ScalarTypes ∪ cw2376RectTypes) cw2376CentralTypes :=
    Finset.disjoint_union_left.mpr ⟨hSC, hRC⟩
  have hSRCD : Disjoint
      (cw2376ScalarTypes ∪ cw2376RectTypes ∪ cw2376CentralTypes)
      cw2376CoupledTypes :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨hSD, hRD⟩, hCD⟩
  have hSRf := Finset.disjoint_filter_filter
    (p := fun σ : Fin 3 → Fin 5 => σ i = r)
    (q := fun σ : Fin 3 → Fin 5 => σ i = r) hSR
  have hSRCf := Finset.disjoint_filter_filter
    (p := fun σ : Fin 3 → Fin 5 => σ i = r)
    (q := fun σ : Fin 3 → Fin 5 => σ i = r) hSRC
  have hSRCDf := Finset.disjoint_filter_filter
    (p := fun σ : Fin 3 → Fin 5 => σ i = r)
    (q := fun σ : Fin 3 → Fin 5 => σ i = r) hSRCD
  simp only [Finset.filter_union] at hSRCf hSRCDf
  simp only [S, Finset.filter_union]
  rw [Finset.sum_union hSRCDf, Finset.sum_union hSRCf,
    Finset.sum_union hSRf]
  have hscalarSum :
      (∑ σ ∈ cw2376ScalarTypes.filter (fun σ => σ i = r),
        cw2376ProfileMultiplicity m σ) =
      (cw2376ScalarTypes.filter (fun σ => σ i = r)).card * (699 * m) := by
    calc
      (∑ σ ∈ cw2376ScalarTypes.filter (fun σ => σ i = r),
          cw2376ProfileMultiplicity m σ) =
          ∑ _σ ∈ cw2376ScalarTypes.filter (fun σ => σ i = r),
            699 * m := by
              apply Finset.sum_congr rfl
              intro σ hσ
              exact profileMultiplicity_of_mem_scalar m
                (Finset.mem_filter.mp hσ).1
      _ = (cw2376ScalarTypes.filter (fun σ => σ i = r)).card *
          (699 * m) := by simp
  have hrectSum :
      (∑ σ ∈ cw2376RectTypes.filter (fun σ => σ i = r),
        cw2376ProfileMultiplicity m σ) =
      (cw2376RectTypes.filter (fun σ => σ i = r)).card * (37518 * m) := by
    calc
      (∑ σ ∈ cw2376RectTypes.filter (fun σ => σ i = r),
          cw2376ProfileMultiplicity m σ) =
          ∑ _σ ∈ cw2376RectTypes.filter (fun σ => σ i = r),
            37518 * m := by
              apply Finset.sum_congr rfl
              intro σ hσ
              exact profileMultiplicity_of_mem_rect m
                (Finset.mem_filter.mp hσ).1
      _ = (cw2376RectTypes.filter (fun σ => σ i = r)).card *
          (37518 * m) := by simp
  have hcentralSum :
      (∑ σ ∈ cw2376CentralTypes.filter (fun σ => σ i = r),
        cw2376ProfileMultiplicity m σ) =
      (cw2376CentralTypes.filter (fun σ => σ i = r)).card * (307638 * m) := by
    calc
      (∑ σ ∈ cw2376CentralTypes.filter (fun σ => σ i = r),
          cw2376ProfileMultiplicity m σ) =
          ∑ _σ ∈ cw2376CentralTypes.filter (fun σ => σ i = r),
            307638 * m := by
              apply Finset.sum_congr rfl
              intro σ hσ
              exact profileMultiplicity_of_mem_central m
                (Finset.mem_filter.mp hσ).1
      _ = (cw2376CentralTypes.filter (fun σ => σ i = r)).card *
          (307638 * m) := by simp
  have hcoupledSum :
      (∑ σ ∈ cw2376CoupledTypes.filter (fun σ => σ i = r),
        cw2376ProfileMultiplicity m σ) =
      (cw2376CoupledTypes.filter (fun σ => σ i = r)).card * (616627 * m) := by
    calc
      (∑ σ ∈ cw2376CoupledTypes.filter (fun σ => σ i = r),
          cw2376ProfileMultiplicity m σ) =
          ∑ _σ ∈ cw2376CoupledTypes.filter (fun σ => σ i = r),
            616627 * m := by
              apply Finset.sum_congr rfl
              intro σ hσ
              exact profileMultiplicity_of_mem_coupled m
                (Finset.mem_filter.mp hσ).1
      _ = (cw2376CoupledTypes.filter (fun σ => σ i = r)).card *
          (616627 * m) := by simp
  rw [hscalarSum, hrectSum, hcentralSum, hcoupledSum]
  rw [scalar_filter_card i r, rect_filter_card i r,
    central_filter_card i r, coupled_filter_card i r]
  fin_cases r <;>
    norm_num [expectedMarginalMultiplicity, scalarMarginalCard,
      rectMarginalCard, centralMarginalCard, coupledMarginalCard] <;>
    omega

theorem solution
    (m : ℕ) (a : CW2376ExactProfileAddress m) :
    ∀ i : Fin 3,
      (Finset.univ.filter (fun j => a.1 i j = (0 : Fin 5))).card =
          384072 * m ∧
      (Finset.univ.filter (fun j => a.1 i j = (1 : Fin 5))).card =
          1308290 * m ∧
      (Finset.univ.filter (fun j => a.1 i j = (2 : Fin 5))).card =
          1231903 * m ∧
      (Finset.univ.filter (fun j => a.1 i j = (3 : Fin 5))).card =
          75036 * m ∧
      (Finset.univ.filter (fun j => a.1 i j = (4 : Fin 5))).card =
          699 * m := by
  intro i
  repeat' rw [exactProfile_marginal_count m a i]
  constructor
  · simpa [expectedMarginalMultiplicity] using
      profileMultiplicity_sum_marginal m i (0 : Fin 5)
  constructor
  · simpa [expectedMarginalMultiplicity] using
      profileMultiplicity_sum_marginal m i (1 : Fin 5)
  constructor
  · simpa [expectedMarginalMultiplicity] using
      profileMultiplicity_sum_marginal m i (2 : Fin 5)
  constructor
  · simpa [expectedMarginalMultiplicity] using
      profileMultiplicity_sum_marginal m i (3 : Fin 5)
  · simpa [expectedMarginalMultiplicity] using
      profileMultiplicity_sum_marginal m i (4 : Fin 5)
